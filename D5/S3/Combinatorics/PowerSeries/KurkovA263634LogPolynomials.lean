/- GID: D5/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/KurkovA263634LogPolynomials
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kurkov's universal logarithmic-polynomial recursion. -/

/-
result:
  proof_shape: content
  escape_witness: quotient_jet, the simultaneous induction over all positive columns.
  admission_basis: open-problem-resolution (#26373; Proved)
  Direct frozen dependencies: D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums.logarithmic_derivative;
    declaration statement_id unavailable in the supplied base report.
Unfinished four-slot escape audit: https://github.com/the-omega-institute/trureturing/issues/26975
The source generating function is stated with PowerSeries.logOf sourceSeries;
no forwarding logarithm or inverse declaration is introduced.
Private declarations below are consumed helpers. Their proof_shape is bind-only
except quotient_jet (content); none supplies a separate admission basis.
map_derivative: proof_shape: bind-only; escape_witness: none; consumers: polynomial_logarithmic_derivative; Direct frozen dependencies: none.
map_logOf: proof_shape: bind-only; escape_witness: none; consumers: polynomial_logarithmic_derivative; Direct frozen dependencies: none.
polynomial_logarithmic_derivative: proof_shape: bind-only; escape_witness: none; consumers: logarithm_derivative; Direct frozen dependencies: PositiveNewtonSums.logarithmic_derivative.
source_constant: proof_shape: bind-only; escape_witness: none; consumers: source_inverse, logarithm_derivative, source_family_exists; Direct frozen dependencies: none.
factorial_cancel: proof_shape: bind-only; escape_witness: none; consumers: inv_factorial_cancel, source_jet, source_family_jet; Direct frozen dependencies: none.
inv_factorial_cancel: proof_shape: bind-only; escape_witness: none; consumers: source_family_exists; Direct frozen dependencies: none.
jet_coeff: proof_shape: bind-only; escape_witness: none; consumers: jet_sub, jet_mul, source_jet, source_family_exists, source_family_jet; Direct frozen dependencies: none.
jet_derivative: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet_step, result; Direct frozen dependencies: none.
jet_sub: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet_step; Direct frozen dependencies: none.
jet_mul: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet_step; Direct frozen dependencies: none.
source_inverse: proof_shape: bind-only; escape_witness: none; consumers: quotient_product, quotient_derivative, logarithm_derivative; Direct frozen dependencies: none.
inverse_constant: proof_shape: bind-only; escape_witness: none; consumers: quotient_initial; Direct frozen dependencies: none.
quotient_product: proof_shape: bind-only; escape_witness: none; consumers: quotient_derivative; Direct frozen dependencies: none.
quotient_derivative: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet_step; Direct frozen dependencies: none.
source_jet: proof_shape: bind-only; escape_witness: none; consumers: quotient_initial; Direct frozen dependencies: none.
quotient_initial: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet; Direct frozen dependencies: none.
quotient_jet_step: proof_shape: bind-only; escape_witness: none; consumers: quotient_jet; Direct frozen dependencies: none.
quotient_jet: proof_shape: content; escape_witness: quotient_jet; consumers: result; Direct frozen dependencies: none.
logarithm_derivative: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: PositiveNewtonSums.logarithmic_derivative.
source_family_exists: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
source_family_jet: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none.
-/

import D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The logarithmic-polynomial recursion of OEIS A263634 -/
namespace D5.S3.Combinatorics.PowerSeries.KurkovA263634LogPolynomials

/-- The source series 1 + sum of x_i t^i/i! over i >= 1. -/
noncomputable def sourceSeries : PowerSeries (MvPolynomial ℕ ℚ) :=
  PowerSeries.mk fun i =>
    if i = 0 then 1
    else MvPolynomial.C ((i.factorial : ℚ)⁻¹) * MvPolynomial.X i

/-- The defining exponential generating function for the family L_n.
The auxiliary value at index zero is zero, as in the logarithmic series. -/
def IsSourceFamily (L : ℕ → (MvPolynomial ℕ ℚ)) : Prop :=
  L 0 = 0 ∧
    (PowerSeries.logOf sourceSeries) = PowerSeries.mk (fun n =>
      MvPolynomial.C ((n.factorial : ℚ)⁻¹) * L n)

/-- Kurkov's array, with row zero extended by zero outside the source domain.
In the last branch, source n is m+2 and source summation index j is r+1. -/
noncomputable def R : ℕ → ℕ → (MvPolynomial ℕ ℚ)
  | 0, _ => 0
  | 1, k => MvPolynomial.X k
  | m + 2, k =>
      R (m + 1) (k + 1) -
        ∑ r : Fin (m + 1),
          MvPolynomial.C (m.choose r.val : ℚ) *
            R (r.val + 1) k * R (m - r.val + 1) 1
termination_by n _ => n
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Existence of the implicitly specified family and the universal polynomial identity. -/
def claim : Prop :=
  (∃ L : ℕ → (MvPolynomial ℕ ℚ), IsSourceFamily L) ∧
    ∀ (L : ℕ → (MvPolynomial ℕ ℚ)), IsSourceFamily L →
      ∀ (n : ℕ), 1 ≤ n → R n 1 = L n

end D5.S3.Combinatorics.PowerSeries.KurkovA263634LogPolynomials

open PowerSeries
open D5.S3.Combinatorics.PowerSeries.PositiveNewtonSums (logarithmic_derivative)
open scoped BigOperators
namespace D5.S3.Combinatorics.PowerSeries.KurkovA263634LogPolynomials
noncomputable section

private lemma map_derivative (e : (MvPolynomial ℕ ℚ) →+* ℚ) (f : PowerSeries (MvPolynomial ℕ ℚ)) :
    PowerSeries.map e (PowerSeries.derivative f) =
      PowerSeries.derivative (PowerSeries.map e f) := by
  ext n
  simp [coeff_map, coeff_derivative]

private lemma map_logOf (e : (MvPolynomial ℕ ℚ) →+* ℚ) (f : PowerSeries (MvPolynomial ℕ ℚ))
    (hf : constantCoeff f = 1) :
    PowerSeries.map e (PowerSeries.logOf f) = PowerSeries.logOf (PowerSeries.map e f) := by
  have hs : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  have h := PowerSeries.map_subst hs (h := e) (PowerSeries.log (MvPolynomial ℕ ℚ))
  change PowerSeries.map e ((PowerSeries.log (MvPolynomial ℕ ℚ)).subst (f - 1)) =
    ((PowerSeries.log (MvPolynomial ℕ ℚ)).map e).subst (PowerSeries.map e (f - 1)) at h
  simpa only [logOf_eq, PowerSeries.map_log, map_sub, map_one] using h

private lemma polynomial_logarithmic_derivative (f : PowerSeries (MvPolynomial ℕ ℚ))
    (hf : constantCoeff f = 1) :
    PowerSeries.derivative (PowerSeries.logOf f) * f = PowerSeries.derivative f := by
  apply PowerSeries.ext
  intro n
  apply MvPolynomial.funext
  intro x
  let e : (MvPolynomial ℕ ℚ) →+* ℚ := MvPolynomial.eval x
  have hc : constantCoeff (PowerSeries.map e f - 1) = 0 := by
    rw [map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, hf, map_one, sub_self]
  have h := logarithmic_derivative (PowerSeries.map e f - 1) hc
  have hu : 1 + (PowerSeries.map e f - 1) = PowerSeries.map e f :=
    add_sub_cancel 1 (PowerSeries.map e f)
  have hm : PowerSeries.map e (PowerSeries.derivative (PowerSeries.logOf f) * f) =
      PowerSeries.map e (PowerSeries.derivative f) := by
    rw [map_mul, map_derivative, map_logOf e f hf, map_derivative]
    rw [logOf_eq]
    simpa only [hu, map_sub, derivative_one, sub_zero] using h
  simpa only [coeff_map] using congrArg (coeff n) hm

private lemma source_constant : constantCoeff sourceSeries = 1 := by
  exact Eq.symm (MvPolynomial.ext 1 (constantCoeff sourceSeries) (congrFun rfl))

private lemma factorial_cancel (n : ℕ) :
    (n.factorial : (MvPolynomial ℕ ℚ)) * MvPolynomial.C ((n.factorial : ℚ)⁻¹) = 1 := by
  rw [← map_natCast MvPolynomial.C n.factorial, ← map_mul]
  simp [Nat.factorial_ne_zero]

private lemma inv_factorial_cancel (n : ℕ) :
    MvPolynomial.C ((n.factorial : ℚ)⁻¹) * (n.factorial : (MvPolynomial ℕ ℚ)) = 1 := by
  rw [mul_comm]
  exact factorial_cancel n

private noncomputable def jet (n : ℕ) (f : PowerSeries (MvPolynomial ℕ ℚ)) : (MvPolynomial ℕ ℚ) :=
  constantCoeff ((PowerSeries.derivative)^[n] f)

private lemma jet_coeff (n : ℕ) (f : PowerSeries (MvPolynomial ℕ ℚ)) :
    jet n f = (n.factorial : (MvPolynomial ℕ ℚ)) * coeff n f := by
  exact constantCoeff_iterate_derivative f n

private lemma jet_derivative (n : ℕ) (f : PowerSeries (MvPolynomial ℕ ℚ)) :
    jet n (PowerSeries.derivative f) = jet (n + 1) f := by
  exact MvPolynomial.ext (jet n (PowerSeries.derivative f)) (jet (n + 1) f) (congrFun rfl)

private lemma jet_sub (n : ℕ) (f g : PowerSeries (MvPolynomial ℕ ℚ)) :
    jet n (f - g) = jet n f - jet n g := by
  simp only [jet_coeff, map_sub, mul_sub]

private lemma jet_mul (n : ℕ) (f g : PowerSeries (MvPolynomial ℕ ℚ)) :
    jet n (f * g) = ∑ r : Fin (n + 1),
      MvPolynomial.C (n.choose r.val : ℚ) * jet r.val f * jet (n - r.val) g := by
  simp only [jet_coeff]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  have hc := congrArg (fun z : ℕ => (z : (MvPolynomial ℕ ℚ)))
    (Nat.choose_mul_factorial_mul_factorial (Fin.is_le r)).symm
  push_cast at hc
  rw [hc, map_natCast]
  ring

private lemma source_inverse : sourceSeries * (invOfUnit sourceSeries 1) = 1 := by
  exact mul_invOfUnit sourceSeries 1 source_constant

private lemma inverse_constant : constantCoeff (invOfUnit sourceSeries 1) = 1 := by
  simp [constantCoeff_invOfUnit]

private noncomputable def quotientSeries (k : ℕ) : PowerSeries (MvPolynomial ℕ ℚ) :=
  ((PowerSeries.derivative)^[k] sourceSeries) * (invOfUnit sourceSeries 1)

private lemma quotient_product (k : ℕ) :
    quotientSeries k * sourceSeries = (PowerSeries.derivative)^[k] sourceSeries := by
  unfold quotientSeries
  calc
    _ = (PowerSeries.derivative)^[k] sourceSeries * (sourceSeries * (invOfUnit sourceSeries 1)) := by ring
    _ = _ := by rw [source_inverse, mul_one]

private lemma quotient_derivative (k : ℕ) :
    PowerSeries.derivative (quotientSeries k) =
      quotientSeries (k + 1) - quotientSeries k * quotientSeries 1 := by
  have h := congrArg (fun f : PowerSeries (MvPolynomial ℕ ℚ) => PowerSeries.derivative f)
    (quotient_product k)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  calc
    _ = (sourceSeries * PowerSeries.derivative (quotientSeries k)) * (invOfUnit sourceSeries 1) := by
      rw [mul_comm sourceSeries, mul_assoc, source_inverse, mul_one]
    _ = (PowerSeries.derivative ((PowerSeries.derivative)^[k] sourceSeries) -
        quotientSeries k * PowerSeries.derivative sourceSeries) * (invOfUnit sourceSeries 1) := by
      rw [← h]
      ring
    _ = _ := by
      simp only [quotientSeries, Function.iterate_succ_apply', Function.iterate_zero_apply]
      ring

private lemma source_jet (k : ℕ) (hk : 1 ≤ k) : jet k sourceSeries = MvPolynomial.X k := by
  rw [jet_coeff, sourceSeries, coeff_mk, ite_eq_right (by omega)]
  rw [← mul_assoc, factorial_cancel, one_mul]

private lemma quotient_initial (k : ℕ) (hk : 1 ≤ k) :
    jet 0 (quotientSeries k) = MvPolynomial.X k := by
  change constantCoeff (((PowerSeries.derivative)^[k] sourceSeries) * (invOfUnit sourceSeries 1)) = _
  rw [map_mul, inverse_constant, mul_one]
  exact source_jet k hk

private lemma quotient_jet_step (m k : ℕ) :
    jet (m + 1) (quotientSeries k) = jet m (quotientSeries (k + 1)) -
      ∑ r : Fin (m + 1), MvPolynomial.C (m.choose r.val : ℚ) *
        jet r.val (quotientSeries k) * jet (m - r.val) (quotientSeries 1) := by
  rw [← jet_derivative, quotient_derivative, jet_sub, jet_mul]

private lemma quotient_jet (n k : ℕ) (hk : 1 ≤ k) :
    R (n + 1) k = jet n (quotientSeries k) := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    cases n with
    | zero =>
      change R 1 k = _
      rw [R]
      exact (quotient_initial k hk).symm
    | succ m =>
      rw [R, quotient_jet_step, ih m (by omega) (k + 1) (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [ih r.val (by omega) k hk, ih (m - r.val) (by omega) 1 (by omega)]

private lemma logarithm_derivative :
    PowerSeries.derivative (PowerSeries.logOf sourceSeries) = quotientSeries 1 := by
  have h := polynomial_logarithmic_derivative sourceSeries source_constant
  change PowerSeries.derivative (PowerSeries.logOf sourceSeries) = _
  calc
    _ = (PowerSeries.derivative (PowerSeries.logOf sourceSeries) * sourceSeries) *
        (invOfUnit sourceSeries 1) := by rw [mul_assoc, source_inverse, mul_one]
    _ = _ := by rw [h]; rfl

private lemma source_family_exists : ∃ L : ℕ → (MvPolynomial ℕ ℚ), IsSourceFamily L := by
  refine ⟨fun n => jet n (PowerSeries.logOf sourceSeries), ?_, ?_⟩
  · change constantCoeff (PowerSeries.logOf sourceSeries) = 0
    exact constantCoeff_logOf source_constant
  · apply PowerSeries.ext
    intro n
    rw [coeff_mk]
    change coeff n (PowerSeries.logOf sourceSeries) = MvPolynomial.C ((n.factorial : ℚ)⁻¹) * jet n (PowerSeries.logOf sourceSeries)
    rw [jet_coeff, ← mul_assoc, inv_factorial_cancel, one_mul]

private lemma source_family_jet (L : ℕ → (MvPolynomial ℕ ℚ)) (hL : IsSourceFamily L) (n : ℕ) :
    jet n (PowerSeries.logOf sourceSeries) = L n := by
  rw [jet_coeff, hL.2, coeff_mk, ← mul_assoc, factorial_cancel, one_mul]

theorem result : claim := by
  refine ⟨source_family_exists, ?_⟩
  intro L hL n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [quotient_jet m 1 (by omega), ← logarithm_derivative, jet_derivative]
  exact source_family_jet L hL (m + 1)

end
end D5.S3.Combinatorics.PowerSeries.KurkovA263634LogPolynomials
