/- GID: D5/S3/Weil/ZetaBridge/ActualPairedReciprocal
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualPairedReciprocal
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Both actual exterior signs and exact reciprocal polynomials retain the entire paired infinite tail. -/

import D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
import Mathlib.Algebra.Polynomial.BigOperators

noncomputable section
open Polynomial MeasureTheory Set
open scoped Interval BigOperators ComplexConjugate
namespace D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingParityGram
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Analytic.PolynomialReciprocalBounds

private def reflect (A : ℂ[X]) : ℂ[X] := A.comp (-X)
private def plusF (A B : ℂ[X]) : ℂ[X] := A+C ((Real.pi/4:ℝ):ℂ)*B
private def minusF (A B : ℂ[X]) : ℂ[X] := reflect A-C ((Real.pi/4:ℝ):ℂ)*reflect B
private def minusG (B : ℂ[X]) : ℂ[X] := -reflect B

def pairedTerm (c N : ℕ) (A B : ℂ[X]) (j : ℕ) : ℝ :=
  let m := N+j+1
  let t : ℝ := (N:ℝ)/m
  (‖value A t-(arithmeticBoundarySymbol c (m:ℤ):ℂ)*value B t‖^2+
    ‖value A (-t)-(arithmeticBoundarySymbol c (-(m:ℤ)):ℂ)*value B (-t)‖^2)/(m:ℝ)^2

def pairedEnergy (c : ℕ) (A B : ℂ[X]) : ℝ :=
  functionEnergy c (plusF A B) B+functionEnergy c (minusF A B) (minusG B)

private lemma reflect_degree (A : ℂ[X]) : (reflect A).natDegree ≤ A.natDegree := by
  simpa only [reflect,natDegree_neg,natDegree_X,mul_one] using
    (Polynomial.natDegree_comp_le (p := A) (q := -(X:ℂ[X])))

private lemma paired_degrees {d : ℕ} (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) :
    (plusF A B).natDegree < d ∧ (minusF A B).natDegree < d ∧ (minusG B).natDegree < d := by
  have hb : (C ((Real.pi/4:ℝ):ℂ)*B).natDegree < d :=
    (Polynomial.natDegree_C_mul_le _ _).trans_lt hB
  have ha' := (reflect_degree A).trans_lt hA
  have hb' := (reflect_degree B).trans_lt hB
  have hm : (C ((Real.pi/4:ℝ):ℂ)*reflect B).natDegree < d :=
    (Polynomial.natDegree_C_mul_le _ _).trans_lt hb'
  exact ⟨(Polynomial.natDegree_add_le _ _).trans_lt (max_lt hA hb),
    (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt ha' hm), by simpa [minusG] using hb'⟩

private lemma pairedTerm_exact {c N : ℕ} (A B : ℂ[X]) (j : ℕ) :
    pairedTerm c N A B j = fullTerm c N (plusF A B) B j+
      fullTerm c N (minusF A B) (minusG B) j := by
  let t : ℝ := (N:ℝ)/(N+j+1:ℕ)
  have hs := actual_symbol_split (c := c) (m := N+j+1) (by omega)
  have hp : value A t-(arithmeticBoundarySymbol c ((N+j+1:ℕ):ℤ):ℂ)*value B t =
      value (plusF A B) t+
        ((primeSymbol c ((N+j+1:ℕ):ℤ)+delta c (N+j+1):ℝ):ℂ)*value B t := by
    rw [hs]
    simp only [value, plusF, eval_add, eval_mul, eval_C,
      Complex.ofReal_neg, Complex.ofReal_add]
    ring
  have hn : value A (-t)-(arithmeticBoundarySymbol c (-((N+j+1:ℕ):ℤ)):ℂ)*value B (-t) =
      value (minusF A B) t+
        ((primeSymbol c ((N+j+1:ℕ):ℤ)+delta c (N+j+1):ℝ):ℂ)*value (minusG B) t := by
    rw [arithmetic_boundary_symbol_neg, hs]
    simp only [value, minusF, minusG, reflect, eval_sub, eval_mul, eval_C,
      eval_comp, eval_neg, eval_X, Complex.ofReal_neg, Complex.ofReal_add]
    ring
  dsimp only [pairedTerm, fullTerm]
  rw [hp, hn, add_div]

/-- Both exterior signs, with the actual full pole/Gamma/prime symbol. -/
theorem actual_paired_symbol_enclosure {c d N : ℕ} (hc : 3 ≤ c) (hd : 1 ≤ d)
    (hN : d^2 ≤ N) (A B : ℂ[X]) (hA : A.natDegree < d) (hB : B.natDegree < d) :
    Summable (pairedTerm c N A B) ∧
    |(N:ℝ)*(∑' j : ℕ,pairedTerm c N A B j)-pairedEnergy c A B| ≤
      (d:ℝ)^2*U c/(N:ℝ)*pairedEnergy c A B := by
  obtain ⟨hp,hm,hg⟩ := paired_degrees A B hA hB
  have hplus := actual_full_symbol_enclosure hc hd hN (plusF A B) B hp hB
  have hminus := actual_full_symbol_enclosure hc hd hN (minusF A B) (minusG B) hm hg
  rw [← functionEnergy_integral] at hplus hminus
  have hs : Summable (pairedTerm c N A B) :=
    (hplus.1.add hminus.1).congr (fun j => (pairedTerm_exact A B j).symm)
  refine ⟨hs, ?_⟩
  simp_rw [pairedTerm_exact]
  rw [hplus.1.tsum_add hminus.1]
  have he : (N:ℝ)*((∑' j,fullTerm c N (plusF A B) B j)+
      (∑' j,fullTerm c N (minusF A B) (minusG B) j))-pairedEnergy c A B =
      ((N:ℝ)*(∑' j,fullTerm c N (plusF A B) B j)-functionEnergy c (plusF A B) B)+
      ((N:ℝ)*(∑' j,fullTerm c N (minusF A B) (minusG B) j)-
        functionEnergy c (minusF A B) (minusG B)) := by unfold pairedEnergy; ring
  rw [he]
  refine (abs_add_le _ _).trans ((add_le_add hplus.2 hminus.2).trans_eq ?_)
  unfold pairedEnergy
  ring

/-- Reversal/dilation in (7.2), written with one reciprocal coefficient. -/
def reciprocalPolynomial (d N : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ r ∈ Finset.range d, C (P.coeff r/(N:ℂ)^(d-1-r))*X^(d-1-r)

lemma reciprocalPolynomial_degree {d N : ℕ} (hd : 1 ≤ d) (P : ℂ[X]) :
    (reciprocalPolynomial d N P).natDegree < d := by
  apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_)
    (show d-1 < d by omega)
  intro r hr
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

/-- Exact evaluation at every nonzero complex m, including negative integers. -/
theorem reciprocalPolynomial_exact {d N : ℕ} (hd : 1 ≤ d) (hN : 0 < N)
    (P : ℂ[X]) (hP : P.natDegree < d) (m : ℂ) (hm : m ≠ 0) :
    m^(d-1)*(reciprocalPolynomial d N P).eval ((N:ℂ)/m) = P.eval m := by
  have hn : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [reciprocalPolynomial,Polynomial.eval_finsetSum,Finset.mul_sum,
    Polynomial.eval_eq_sum_range' hP]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ d-1 := by have := Finset.mem_range.mp hr; omega
  have hsplit : d-1-r+r = d-1 := Nat.sub_add_cancel hr'
  simp only [eval_mul,eval_C,eval_pow,eval_X,div_pow]
  have hpN := pow_ne_zero (d-1-r) hn
  have hpm := pow_ne_zero (d-1-r) hm
  have hpow : m^(d-1) = m^(d-1-r)*m^r := by rw [← pow_add,hsplit]
  rw [hpow]
  field_simp [hpN,hpm]
  <;> ring

end D5.S3.Weil.ZetaBridge.ActualPairedReciprocal

namespace D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Analytic.PolynomialReciprocalBounds

lemma pairedEnergy_integral (c : ℕ) (A B : ℂ[X]) : pairedEnergy c A B =
    ∫ t in (0:ℝ)..1,
      (‖value A t+((Real.pi/4:ℝ):ℂ)*value B t‖^2+
       ‖value A (-t)-((Real.pi/4:ℝ):ℂ)*value B (-t)‖^2+
       mean c*(‖value B t‖^2+‖value B (-t)‖^2)) := by
  have h1 : IntervalIntegrable (fun t : ℝ => ‖value (plusF A B) t‖^2+mean c*‖value B t‖^2) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => ‖value (plusF A B) t‖^2+mean c*‖value B t‖^2)).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t : ℝ => ‖value (minusF A B) t‖^2+mean c*‖value (minusG B) t‖^2) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => ‖value (minusF A B) t‖^2+mean c*‖value (minusG B) t‖^2)).intervalIntegrable 0 1
  unfold pairedEnergy
  rw [functionEnergy_integral,functionEnergy_integral,← intervalIntegral.integral_add h1 h2]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [plusF,minusF,minusG,reflect,value,eval_add,eval_sub,eval_mul,eval_C,
    eval_comp,eval_neg,eval_X,norm_neg,Complex.ofReal_neg]
  ring

end D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
