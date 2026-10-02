/- GID: D5/S3/ArithSums/LogLaplacianEvenResidueVanishing
   generality: I
   mirror-B: D5/B/S3/ArithSums/LogLaplacianEvenResidueVanishing
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The Rosenzweig-Stanfill residue bracket vanishes for every even index. -/
/-
result:
  proof_shape: content
  escape_witness: RS16Series.linear_ODE_unique; RS16Translation.F_translation; bernoulli_annihilates; primary_square_inverse.
  admission_basis: open-problem-resolution (#11546; Proved)
Direct frozen dependencies: CompositionalIterateCongruence.mobius;
  StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion.
Information-escape registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Combinatorics.Enumerative.Stirling
namespace D5.S3.ArithSums
/-!
Rosenzweig–Stanfill Open Problem 1.6(iv), arXiv:2606.04225v1, issue #11546.
The primary c-array uses Eq:Polylogrec and the recursive definition in Theorem 1.5,
including the separate Bernoulli formula at α = π/2. Partial ordinary Bell
polynomials use the paper's multinomial profile sum. Mathlib's Bernoulli numbers
have B₁ = -1/2. The finite d-array, b-convolution and bracket are the displayed
paper formulas.
The proof uses formal power series; all coefficient identities involve finite
sums. The square inverse-denominator identity is derived from the primary
polylogarithm recursion, rather than assumed as a generating-function definition.
Bernoulli translation at 1/2 then annihilates the odd derivative of the centered
even series for every even m. No analytic convergence assertion is needed.
-/
namespace LogLaplacianEvenResidueVanishing
noncomputable def bellProfiles (n k : ℕ) : Finset (Fin (n-k+1) → Fin (k+1)) :=
  Finset.univ.filter fun j =>
    (∑ i, (j i : ℕ)) = k ∧ (∑ i, (i.val+1) * (j i : ℕ)) = n
noncomputable def bell (n k : ℕ) (s : ℕ → ℂ) : ℂ :=
  ∑ j ∈ bellProfiles n k, ((k.factorial : ℂ) / ∏ i, ((j i).val.factorial : ℂ)) * ∏ i, s (i.val+1) ^ (j i).val
noncomputable def negativePolylog (j : ℕ) (z : ℂ) : ℂ :=
  ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w)^[j]) (fun w => w/(1-w)) z
end LogLaplacianEvenResidueVanishing
open LogLaplacianEvenResidueVanishing
set_option maxRecDepth 2000
open scoped BigOperators
open Finset Nat
open PowerSeries
namespace RS16Series
open PowerSeries
private noncomputable def expScale (t : ℂ) : PowerSeries ℂ := rescale t (exp ℂ)
end RS16Series
namespace RS16Series
open PowerSeries
private lemma linear_ODE_unique (F G R : PowerSeries ℂ) (hF : derivative ℂ F = F*R) (hG : derivative ℂ G = G*R) (h0 : constantCoeff F = constantCoeff G) : F = G := by
  have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have hFn := congrArg (coeff n) hF
      have hGn := congrArg (coeff n) hG
      rw [coeff_derivative, local_RS16Series_coeff_product] at hFn hGn
      have he : (∑ q ∈ range (n+1), coeff q F * coeff (n-q) R) = ∑ q ∈ range (n+1), coeff q G * coeff (n-q) R := by apply sum_congr rfl; intro q hq; rw [ih q (mem_range.mp hq)]
      have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact mul_right_cancel₀ hn (hFn.trans (he.trans hGn.symm))
end RS16Series
open scoped BigOperators
open Finset Nat
namespace RS16Bernoulli
private noncomputable def residuePolynomial (n : ℕ) (s : ℕ → ℂ) (t : ℂ) : ℂ :=
  ∑ k ∈ range (n+1), ((-1 : ℂ)^k / (k.factorial : ℂ)) * bell n k s * t^k
private noncomputable def entrySeries (s : ℕ → ℂ) : PowerSeries ℂ := mk fun n => if n=0 then 0 else s n
private noncomputable def pSeries (s : ℕ → ℂ) (t : ℂ) : PowerSeries ℂ :=
  (exp ℂ).subst (C (-t) * entrySeries s)
end RS16Bernoulli
open scoped BigOperators
open Finset Nat
namespace RS16Convolution
private noncomputable def coefficientConvolution (d : ℕ → ℕ → ℂ) (c : ℕ → ℂ) (i k : ℕ) : ℂ :=
  ∑ j ∈ range (i/2+1), d (k+j) k * c (i-2*j)
private noncomputable def weightedConvolution (d : ℕ → ℕ → ℂ) (c w : ℕ → ℂ) (l : ℕ) : ℂ :=
  ∑ k ∈ range (l/2+1), w k * coefficientConvolution d c (l-2*k) k
private noncomputable def E (d : ℕ → ℕ → ℂ) (w : ℕ → ℂ) (j : ℕ) : ℂ :=
  if Even j then ∑ k ∈ range (j/2+1), w k * d (j/2) k else 0
end RS16Convolution
open scoped BigOperators
open Finset Nat
namespace RS16Center
open PowerSeries
private noncomputable def center : PowerSeries ℚ := mk fun n =>
  if n = 0 then 1/2 else ((2 : ℚ)^(n+1)-1) * bernoulli (n+1) / ((n+1)! : ℚ)
end RS16Center
namespace RS16Translation
open PowerSeries
private noncomputable def U (t : ℂ) : PowerSeries ℂ := rescale t (mk 1)
private noncomputable def BT (t : ℂ) : PowerSeries ℂ :=
  mk fun n => (Polynomial.aeval t) (Polynomial.bernoulli (n+1))
private noncomputable def S (m : ℕ) (t : ℂ) : PowerSeries ℂ :=
  mk fun n => if n=0 then 0 else -(m : ℂ)*(Polynomial.aeval t) (Polynomial.bernoulli n)/(n : ℂ)
private noncomputable def F (m : ℕ) (t : ℂ) : PowerSeries ℂ := (exp ℂ).subst (S m t)
private lemma F_translation (m : ℕ) (t : ℂ) : F m t = (1 - C t * X) ^ m * (F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) := by
  have local_RS16Series_coeff_mul_subst (F G V : PowerSeries ℂ) (hG : constantCoeff G = 0) (n : ℕ) : coeff n (V * F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff n (V * G^r) := by
    have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    classical
    have hg : HasSubst G := HasSubst.of_constantCoeff_zero' hG
    have hex (q : ℕ) (hq : q ≤ n) : coeff q (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff q (G^r) := by
      rw [coeff_subst' hg]; apply finsum_eq_sum_of_support_subset; intro r hr
      by_contra hnr
      have hnr' : n < r := by simp only [Finset.mem_coe, mem_range] at hnr; omega
      have hz : coeff q (G^r) = 0 := by apply coeff_of_lt_order; exact lt_of_lt_of_le (by exact_mod_cast (lt_of_le_of_lt hq hnr')) (le_order_pow_of_constantCoeff_eq_zero r hG)
      exact hr (by simp [hz])
    rw [local_RS16Series_coeff_product]
    have hterms : ∀ q ∈ range (n+1), coeff (n-q) (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r) := by intro q hq; exact hex _ (Nat.sub_le _ _)
    have hs : (∑ q ∈ range (n+1), coeff q V * coeff (n-q) (F.subst G)) = ∑ q ∈ range (n+1), coeff q V * (∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r)) := by apply sum_congr rfl; intro q hq; rw [hterms q hq]
    rw [hs]; simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro r hr; rw [local_RS16Series_coeff_product, mul_sum]; apply sum_congr rfl; intro q hq; ring
  have local_bernoulli_tail_translation (t : ℂ) : BT t = C t * U t + U t ^ 2 * (BT 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) := by
    have hY0 : constantCoeff (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) = 0 := by simp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius]
    have hcU (n : ℕ) : coeff n (U t) = t^n := by simp [U]
    have hcUp (d n : ℕ) : coeff n (U t ^ (d+1)) = t^n*(Nat.choose (d+n) d : ℂ) := by dsimp [U]; rw [← map_pow, mk_one_pow_eq_mk_choose_add]; simp
    have hBT0 (r : ℕ) : coeff r (BT 0) = (bernoulli (r+1) : ℂ) := by simp [BT, Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_bernoulli]
    have hcUY (n r : ℕ) (hr : r ≤ n) : coeff n (U t ^ 2 * (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)^r) = t^(n-r)*(Nat.choose (n+1) (r+1) : ℂ) := by
      have he : U t ^ 2 * (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)^r = X^r * U t^(r+2) := by change U t ^ 2 * (X * U t)^r = X^r * U t^(r+2); rw [mul_pow, pow_add]; ring
      rw [he]
      have hn : n = (n-r)+r := by omega
      conv_lhs => arg 1; rw [hn]
      rw [coeff_X_pow_mul]
      have he' : r+2 = (r+1)+1 := by omega
      rw [he', hcUp, show r+1+(n-r) = n+1 by omega]
    ext n; rw [map_add, coeff_C_mul, hcU, local_RS16Series_coeff_mul_subst _ _ _ hY0]
    have hh : (∑ r ∈ range (n+1), coeff r (BT 0) * coeff n (U t ^ 2 * D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t^r)) = ∑ r ∈ range (n+1), (bernoulli (r+1) : ℂ)* (t^(n-r)*(Nat.choose (n+1) (r+1) : ℂ)) := by apply sum_congr rfl; intro r hr; rw [hBT0, hcUY _ _ (Nat.le_of_lt_succ (mem_range.mp hr))]
    rw [hh]; simp only [BT, coeff_mk, Polynomial.bernoulli, map_sum, Polynomial.aeval_monomial]; rw [sum_range_succ']; simp only [Nat.add_sub_add_right, Nat.choose_zero_right, bernoulli_zero, map_mul, map_natCast, map_one, Nat.sub_zero, mul_one, one_mul]
    rw [add_comm]; apply congrArg₂ (·+·)
    · norm_num only [Rat.cast_one]
      rw [pow_succ]; ring
    · apply sum_congr rfl
      intro r hr; change ((bernoulli (r+1) : ℂ)*(Nat.choose (n+1) (r+1) : ℂ))*t^(n-r) = _; ring
  have local_RS16Translation_F_differential (m : ℕ) (t : ℂ) : derivative ℂ (RS16Translation.F m t) = RS16Translation.F m t * (C (-(m : ℂ))*RS16Translation.BT t) ∧ constantCoeff (RS16Translation.F m t) = 1 := by
    have hs0 : constantCoeff (RS16Translation.S m t) = 0 := by simp [RS16Translation.S]
    have hs : HasSubst (RS16Translation.S m t) := HasSubst.of_constantCoeff_zero' hs0
    have hD : derivative ℂ (RS16Translation.S m t) = C (-(m : ℂ))*RS16Translation.BT t := by
      ext n; rw [coeff_derivative, coeff_C_mul]; simp only [RS16Translation.S, RS16Translation.BT, coeff_mk, Nat.succ_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
    constructor
    · rw [RS16Translation.F, derivative_subst hs, derivative_exp, hD]
    · rw [← coeff_zero_eq_constantCoeff_apply, RS16Translation.F]
      have hh := local_RS16Series_coeff_mul_subst (exp ℂ) (RS16Translation.S m t) 1 hs0 0
      simpa using hh
  have hUV : U t * (1 - C t * X) = 1 := by
    have hh := congrArg (rescale t) (mk_one_mul_one_sub_eq_one (S := ℂ))
    have hX := rescale_X t
    simpa only [U, map_mul, map_sub, map_one, hX] using hh
  have hDU : derivative ℂ (U t) = C t * U t^2 := by
    ext n; simp only [coeff_derivative, U, coeff_rescale, coeff_mk, Pi.one_apply, mul_one, coeff_C_mul]; rw [← map_pow, show (2:ℕ) = 1+1 by rfl, mk_one_pow_eq_mk_choose_add]
    simp only [coeff_rescale, coeff_mk, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hDY : derivative ℂ (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) = U t^2 := by
    change derivative ℂ (X * U t) = U t^2
    rw [Derivation.leibniz, derivative_X, hDU]; simp only [smul_eq_mul, mul_one]
    have hh : U t^2 * (1 - C t * X) = U t := by rw [pow_two, mul_assoc, hUV, mul_one]
    linear_combination -hh
  have hDV : derivative ℂ ((1 - C t * X)) = -C t := by simp [map_sub, derivative_one, Derivation.leibniz, smul_eq_mul]
  have hY0 : constantCoeff (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) = 0 := by simp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius]
  have hY : HasSubst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) := HasSubst.of_constantCoeff_zero' hY0
  have hF0 := (local_RS16Translation_F_differential m 0).1
  have hFs : derivative ℂ ((F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) = (F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) * (C (-(m : ℂ))*(BT 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) * U t^2 := by
    rw [derivative_subst hY, hF0, subst_mul hY, subst_mul hY, subst_C, hDY]
    rfl
  have hT : derivative ℂ ((1 - C t * X) ^ m * (F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) = ((1 - C t * X) ^ m * (F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t))*(C (-(m : ℂ))*BT t) := by
    rw [Derivation.leibniz, hFs, derivative_pow, hDV, local_bernoulli_tail_translation t]; simp only [smul_eq_mul]
    have hmcast : (m : PowerSeries ℂ) = C (m : ℂ) := by simp
    rw [hmcast]; simp only [map_neg]
    cases m with
    | zero => simp
    | succ a =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      have hh : (1 - C t * X) ^ (a+1)*U t = (1 - C t * X)^a := by rw [pow_succ, mul_assoc, mul_comm ((1 - C t * X)) (U t), hUV, mul_one]
      have hc : C (-(a+1 : ℂ)) = -C (a+1 : ℂ) := by rw [map_neg]
      linear_combination (C (a+1 : ℂ)*C t*(F (a+1) 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) * hh
  have hT0 : constantCoeff ((1 - C t * X) ^ m * (F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) = 1 := by
    rw [map_mul, map_pow]; simp only [map_sub, map_one, map_mul, constantCoeff_X, mul_zero, sub_zero, one_pow, one_mul]; rw [← coeff_zero_eq_constantCoeff_apply]
    have hh := local_RS16Series_coeff_mul_subst (F m 0) (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t) 1 hY0 0
    calc
      coeff 0 ((F m 0).subst (D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)) = coeff 0 (F m 0) := by simpa using hh
      _ = 1 := by simpa only [coeff_zero_eq_constantCoeff] using (local_RS16Translation_F_differential m 0).2
  apply RS16Series.linear_ODE_unique _ _ _ (local_RS16Translation_F_differential m t).1 hT; rw [(local_RS16Translation_F_differential m t).2, hT0]
end RS16Translation
open scoped BigOperators Topology
open Finset Nat
namespace RS16Polylog
private noncomputable def R (q : ℕ) (z : ℂ) : ℂ := z^q/(1-z)^(q+1)
private noncomputable def finiteLi (n : ℕ) (z : ℂ) : ℂ :=
  (∑ q ∈ range (n+1), (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*R q z) - if n=0 then 1 else 0
private lemma negativePolylog_finite (n : ℕ) (z : ℂ) (hz : z ≠ 1) : negativePolylog n z = finiteLi n z := by
  have local_finiteLi_Euler (n : ℕ) (z : ℂ) (hz : z ≠ 1) : z * deriv (RS16Polylog.finiteLi n) z = RS16Polylog.finiteLi (n+1) z := by
    have hden : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    let dr := fun (q : ℕ) =>
      ((q : ℂ)*z^(q-1)*(1-z)^(q+1)+z^q*(q+1 : ℂ)*(1-z)^q) / ((1-z)^(q+1))^2
    have hR (q : ℕ) : HasDerivAt (RS16Polylog.R q) (dr q) z := by
      have hsub : HasDerivAt (fun w : ℂ => 1-w) (-1) z :=
        (hasDerivAt_id z).const_sub 1
      convert! ((hasDerivAt_id z).pow q).div (hsub.pow (q+1)) (pow_ne_zero _ hden) using 1 <;>
        simp only [RS16Polylog.R, dr, Pi.pow_apply, Pi.div_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one, mul_neg, neg_mul, mul_comm (-1 : ℂ), sub_neg_eq_add, neg_one_mul, mul_assoc]
    have hEuler (q : ℕ) : z*dr q = (q : ℂ)*RS16Polylog.R q z + (q+1 : ℂ)*RS16Polylog.R (q+1) z := by
      dsimp [dr, RS16Polylog.R]
      cases q with
      | zero => simp; field_simp
      | succ q =>
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]; simp_rw [pow_succ]; field_simp <;> ring
    have hsum : HasDerivAt (RS16Polylog.finiteLi n) (∑ q ∈ range (n+1), (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*dr q) z := by
      change HasDerivAt (fun w => (∑ q ∈ range (n+1), (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*RS16Polylog.R q w) - if n=0 then 1 else 0) _ z
      have hh := HasDerivAt.sum (u := range (n+1)) (fun q _ => (hR q).const_mul ((Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)))
      simpa only [Finset.sum_apply] using hh.sub_const (if n=0 then (1:ℂ) else 0)
    rw [hsum.deriv, mul_sum]
    have hdist : (∑ q ∈ range (n+1), z*((Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*dr q)) = (∑ q ∈ range (n+1), (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*(q : ℂ)*RS16Polylog.R q z) + (∑ q ∈ range (n+1), (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*(q+1 : ℂ)*RS16Polylog.R (q+1) z) := by
      rw [← sum_add_distrib]; apply sum_congr rfl; intro q hq
      calc
        _ = (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*(z*dr q) := by ring
        _ = _ := by rw [hEuler]; ring
    rw [hdist]; unfold RS16Polylog.finiteLi; rw [if_neg (Nat.succ_ne_zero n), sub_zero]
    conv_rhs => rw [sum_range_succ']
    simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero]
    have hrec (q : ℕ) : (Nat.stirlingSecond (n+1) (q+1) : ℂ)*((q+1) ! : ℂ) = (Nat.stirlingSecond n (q+1) : ℂ)*((q+1) ! : ℂ)*(q+1 : ℂ) + (Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*(q+1 : ℂ) := by rw [Nat.stirlingSecond_succ_succ, factorial_succ]; push_cast; ring
    simp_rw [hrec, add_mul, sum_add_distrib]; congr 1; rw [sum_range_succ']; simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]; rw [sum_range_succ]; simp only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, zero_mul, add_zero]
    simp only [Nat.cast_add, Nat.cast_one]
  induction n generalizing z with
  | zero =>
    simp [negativePolylog, finiteLi, R]; field_simp; ring
  | succ n ih =>
    have heq : negativePolylog n =ᶠ[𝓝 z] finiteLi n := by
      have hh : ∀ᶠ w in 𝓝 z, w ≠ 1 := eventually_ne_nhds hz
      filter_upwards [hh] with w hw
      exact ih w hw
    rw [negativePolylog, Function.iterate_succ_apply']; change z * deriv (negativePolylog n) z = _; rw [heq.deriv_eq]; exact local_finiteLi_Euler n z hz
end RS16Polylog
namespace RS16ExpStirling
open PowerSeries
private noncomputable def T : PowerSeries ℂ := RS16Series.expScale 1 - 1
end RS16ExpStirling
namespace RS16PolylogGF
open PowerSeries
private noncomputable def V (z : ℂ) : PowerSeries ℂ := C (z/(1-z))*RS16ExpStirling.T
private noncomputable def fullG (z : ℂ) : PowerSeries ℂ :=
  C (1/(1-z)) * (mk (1 : ℕ → ℂ)).subst (V z)
private noncomputable def G (z : ℂ) : PowerSeries ℂ := fullG z - 1
private noncomputable def quad (z : ℂ) : PowerSeries ℂ :=
  C (z/(z-z⁻¹))*rescale (-1) (fullG z) - C (z⁻¹/(z-z⁻¹))*(1-fullG z)
end RS16PolylogGF
open scoped BigOperators
open Finset Nat
namespace LogLaplacianEvenResidueVanishing
noncomputable def s2 (n : ℕ) : ℂ :=
  if n = 0 then 0 else -(bernoulli n : ℂ) / n
noncomputable def p (j : ℕ) (t : ℂ) : ℂ :=
  ∑ k ∈ range (j + 1), (-1 : ℂ)^k / (k ! : ℂ) * bell j k s2 * t^k
/-- The primary recursive coefficient array in Theorem 1.5 and Lemma Sqrt. -/
noncomputable def c (α : ℝ) : ℕ → ℂ
  | 0 => 1 / (2 * (Real.sin α : ℂ))
  | j+1 =>
      if α = Real.pi/2 then ((2 : ℂ)^(j+2)-1) * (bernoulli (j+2) : ℂ) / ((j+2)! : ℂ)
      else (Real.sin α : ℂ) * (-(Complex.I * (Real.cos (2*α) / Real.sin (2*α) : ℂ))^ (if Even (j+1) then 1 else 0) / ((j+1)! : ℂ) * negativePolylog (j+1) (Complex.exp (2*α*Complex.I)) - ∑ q : Fin j, c α (q.val+1) * c α (j-q.val))
  termination_by n => n
  decreasing_by all_goals omega
noncomputable def d (α : ℝ) (j k : ℕ) : ℂ :=
  if k = 0 then (if j = 0 then 1 else 0) else if k ≤ j then (1 / ((2*j) ! : ℂ)) * ∑ ell ∈ Icc k j, (Nat.choose (ell - 1) (k - 1) : ℂ) * (-1 : ℂ)^(ell-k) / (4 : ℂ)^ell / (Real.sin α : ℂ)^(2*ell) * ∑ v ∈ range (2*ell + 1), (-1 : ℂ)^v * (Nat.choose (2*ell) v : ℂ) * ((ell : ℂ) - v)^(2*j) else 0
noncomputable def b (α : ℝ) (i k : ℕ) : ℂ :=
  ∑ j ∈ range (i / 2 + 1), d α (k + j) k * c α (i - 2*j)
noncomputable def w (k : ℕ) : ℂ :=
  (∏ q ∈ range k, ((1/2 : ℂ) + q))^2 / (k ! : ℂ)^2
noncomputable def A (α : ℝ) (ell : ℕ) : ℂ :=
  ∑ k ∈ range (ell / 2 + 1), w k * b α (ell - 2*k) k
noncomputable def paperBracket (m : ℕ) (α : ℝ) : ℂ :=
  (∑ ell ∈ Icc 1 (m + 1), (-1 : ℂ)^ell * (ell ! : ℂ) * p (m + 1 - ell) (-m) * A α ell) + (1/2 : ℂ) * ∑ ell ∈ range (m + 1), (-1 : ℂ)^ell * (ell ! : ℂ) * p (m - ell) (-m) * A α ell
private noncomputable def shifted (α : ℝ) (n : ℕ) : ℂ :=
  ∑ q ∈ range (n + 1), (-1/2 : ℂ)^q / (q ! : ℂ) * A α (n-q)
private noncomputable def derivativeArray (α : ℝ) (j : ℕ) : ℂ :=
  (j + 1 : ℂ) * A α (j+1) - (1/2 : ℂ) * A α j
private noncomputable def annihilates (m : ℕ) : Prop :=
  ∀ k ≤ m, Odd k → (∑ j ∈ range (m + 1), if k ≤ j then (-1 : ℂ)^j * (j ! : ℂ) * p (m-j) (-m) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0) = 0
def claim : Prop :=
  ∀ m : ℕ, Even m → ∀ α : ℝ, 0 < α → α < Real.pi → paperBracket m α = 0
end LogLaplacianEvenResidueVanishing
namespace LogLaplacianEvenResidueVanishing
open PowerSeries
private lemma bernoulli_annihilates (m : ℕ) (hm : Even m) : annihilates m := by
  have local_RS16Series_coeff_mul_subst (F G V : PowerSeries ℂ) (hG : constantCoeff G = 0) (n : ℕ) : coeff n (V * F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff n (V * G^r) := by
    have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    classical
    have hg : HasSubst G := HasSubst.of_constantCoeff_zero' hG
    have hex (q : ℕ) (hq : q ≤ n) : coeff q (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff q (G^r) := by
      rw [coeff_subst' hg]; apply finsum_eq_sum_of_support_subset; intro r hr
      by_contra hnr
      have hnr' : n < r := by simp only [Finset.mem_coe, mem_range] at hnr; omega
      have hz : coeff q (G^r) = 0 := by apply coeff_of_lt_order; exact lt_of_lt_of_le (by exact_mod_cast (lt_of_le_of_lt hq hnr')) (le_order_pow_of_constantCoeff_eq_zero r hG)
      exact hr (by simp [hz])
    rw [local_RS16Series_coeff_product]
    have hterms : ∀ q ∈ range (n+1), coeff (n-q) (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r) := by intro q hq; exact hex _ (Nat.sub_le _ _)
    have hs : (∑ q ∈ range (n+1), coeff q V * coeff (n-q) (F.subst G)) = ∑ q ∈ range (n+1), coeff q V * (∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r)) := by apply sum_congr rfl; intro q hq; rw [hterms q hq]
    rw [hs]; simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro r hr; rw [local_RS16Series_coeff_product, mul_sum]; apply sum_congr rfl; intro q hq; ring
  have local_RS16Bernoulli_bell_truncated_coefficient (n k : ℕ) (s : ℕ → ℂ) : bell n k s = coeff n ((∑ i : Fin (n-k+1), monomial (i.val+1) (s (i.val+1)))^k) := by
    classical
    let L := n-k+1
    let T : PowerSeries ℂ := ∑ i : Fin L, monomial (i.val+1) (s (i.val+1))
    let ps := (Finset.univ : Finset (Fin L)).piAntidiag k
    let qs := ps.filter fun q => (∑ i, (i.val+1)*q i) = n
    have hcoeff : coeff n (T^k) = ∑ q ∈ qs, (Nat.multinomial univ q : ℂ) * ∏ i, s (i.val+1) ^ q i := by
      dsimp [T]; rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]; simp only [qs, ps, sum_filter]; apply sum_congr rfl; intro q hq; simp_rw [monomial_pow]; rw [prod_monomial]
      have hncast : (Nat.multinomial univ q : PowerSeries ℂ) = C (Nat.multinomial univ q : ℂ) := by simp
      rw [hncast, coeff_C_mul, coeff_monomial]
      have hw : ∑ i : Fin L, q i * (i.val+1) = ∑ i : Fin L, (i.val+1) * q i := by apply sum_congr rfl; intro i hi; ring
      rw [hw]
      by_cases h : (∑ i : Fin L, (i.val+1)*q i) = n
      · simp only [h, ↓reduceIte]
      · simp only [h, Ne.symm h, ↓reduceIte, mul_zero]
    rw [hcoeff]; unfold bell; symm
    let toProfile (q : Fin L → ℕ) (hq : q ∈ qs) : Fin L → Fin (k+1) := fun i =>
      ⟨q i, by
        have hsum : (∑ i : Fin L, q i) = k := (mem_piAntidiag.mp (mem_filter.mp hq).1).1
        have hle : q i ≤ ∑ i : Fin L, q i := single_le_sum (fun i _ => Nat.zero_le (q i)) (mem_univ i)
        omega⟩
    apply sum_bij toProfile
    · intro q hq
      simp only [bellProfiles, mem_filter, mem_univ, true_and]; exact ⟨(mem_piAntidiag.mp (mem_filter.mp hq).1).1, (mem_filter.mp hq).2⟩
    · intro q hq q' hq' he
      ext i
      have hh := congrFun he i
      exact congrArg Fin.val hh
    · intro j hj
      have hj' := (mem_filter.mp hj).2
      refine ⟨fun i => (j i).val, ?_, ?_⟩
      · apply mem_filter.mpr
        exact ⟨mem_piAntidiag.mpr ⟨hj'.1, fun _ _ => mem_univ _⟩, hj'.2⟩
      · ext i; rfl
    · intro q hq
      have hsum : (∑ i : Fin L, q i) = k := (mem_piAntidiag.mp (mem_filter.mp hq).1).1
      have hm := Nat.multinomial_spec (Finset.univ : Finset (Fin L)) q
      rw [hsum] at hm
      have hprod : (∏ i : Fin L, ((q i)! : ℂ)) ≠ 0 := by
        apply prod_ne_zero_iff.mpr; intro i hi
        exact_mod_cast factorial_ne_zero (q i)
      have hmult : (Nat.multinomial univ q : ℂ) = (k ! : ℂ)/(∏ i : Fin L, ((q i)! : ℂ)) := by
        apply (eq_div_iff hprod).mpr
        have hm' : (∏ i : Fin L, ((q i)! : ℂ)) * (Nat.multinomial univ q : ℂ) = (k ! : ℂ) := by exact_mod_cast hm
        simpa [mul_comm] using hm'
      simp only [toProfile]; rw [hmult]
  have local_RS16Bernoulli_bell_coefficient (n k : ℕ) (s : ℕ → ℂ) : bell n k s = coeff n (RS16Bernoulli.entrySeries s ^ k) := by
    classical
    let L := n-k+1
    let T : PowerSeries ℂ := ∑ i : Fin L, monomial (i.val+1) (s (i.val+1))
    have hT0 : coeff 0 T = 0 := by simp [T, coeff_monomial]
    have hT (v : ℕ) (hv : 0 < v) (hvL : v ≤ L) : coeff v T = s v := by
      dsimp [T]; rw [map_sum]
      let i : Fin L := ⟨v-1, by omega⟩
      rw [sum_eq_single i]
      · rw [coeff_monomial]
        have hi : i.val+1 = v := by dsimp [i]; omega
        simp [hi]
      · intro j hj hji
        rw [coeff_monomial, if_neg]; intro he; apply hji; apply Fin.ext; dsimp [i]; omega
      · simp
    rw [local_RS16Bernoulli_bell_truncated_coefficient, coeff_pow, coeff_pow]; apply sum_congr rfl; intro q hq
    have hsum : ∑ i ∈ range k, q i = n := (mem_finsuppAntidiag.mp hq).1
    by_cases hzero : ∃ i ∈ range k, q i = 0
    · obtain ⟨i, hi, hiz⟩ := hzero
      have hzT : ∏ j ∈ range k, coeff (q j) T = 0 := by apply prod_eq_zero hi; rw [hiz, hT0]
      have hzS : ∏ j ∈ range k, coeff (q j) (RS16Bernoulli.entrySeries s) = 0 := by apply prod_eq_zero hi; simp [hiz, RS16Bernoulli.entrySeries]
      exact hzT.trans hzS.symm
    · push_neg at hzero
      apply prod_congr rfl; intro i hi
      have hqi : 0 < q i := Nat.pos_of_ne_zero (hzero i hi)
      have hbound : q i ≤ L := by
        have he : (∑ j ∈ (range k).erase i, q j) + q i = n :=
          (sum_erase_add _ _ hi).trans hsum
        have hrest : k-1 ≤ ∑ j ∈ (range k).erase i, q j := by
          have hcard : ∑ j ∈ (range k).erase i, (1 : ℕ) = k-1 := by simp [card_erase_of_mem hi]
          rw [← hcard]; apply sum_le_sum; intro j hj; exact Nat.pos_of_ne_zero (hzero j (mem_of_mem_erase hj))
        dsimp [L]
        have hik : i < k := mem_range.mp hi
        omega
      change coeff (q i) T = _; rw [hT _ hqi hbound]; simp [RS16Bernoulli.entrySeries, hqi.ne']
  have local_RS16Bernoulli_p_coefficient (n : ℕ) (s : ℕ → ℂ) (t : ℂ) : RS16Bernoulli.residuePolynomial n s t = coeff n (RS16Bernoulli.pSeries s t) := by
    classical
    let g := C (-t) * RS16Bernoulli.entrySeries s
    have hg0 : constantCoeff g = 0 := by simp [g, RS16Bernoulli.entrySeries]
    have hg : HasSubst g := HasSubst.of_constantCoeff_zero' hg0
    have hz (k : ℕ) (hk : n < k) : coeff n (g^k) = 0 := by apply coeff_of_lt_order; exact lt_of_lt_of_le (by exact_mod_cast hk) (le_order_pow_of_constantCoeff_eq_zero k hg0)
    have hsupp : Function.support (fun k => coeff k (exp ℂ) • coeff n (g^k)) ⊆ ↑(range (n+1)) := by
      intro k hk
      by_contra hn
      have hkn : n < k := by simp only [Finset.mem_coe, mem_range] at hn; omega
      exact hk (by simp [hz k hkn])
    rw [RS16Bernoulli.pSeries, coeff_subst' hg, finsum_eq_sum_of_support_subset _ hsupp]; unfold RS16Bernoulli.residuePolynomial; apply sum_congr rfl; intro k hk; rw [local_RS16Bernoulli_bell_coefficient]; change _ = coeff k (exp ℂ) * coeff n ((C (-t) * RS16Bernoulli.entrySeries s)^k); rw [mul_pow, ← map_pow, coeff_C_mul]
    simp only [coeff_exp, map_div₀, map_one, map_natCast]; rw [neg_pow]; ring
  have local_RS16Translation_F_coefficient_translation (m n : ℕ) (hnm : n ≤ m) (t : ℂ) : coeff n (RS16Translation.F m t) = ∑ r ∈ range (n+1), coeff r (RS16Translation.F m 0) * ((-t)^(n-r)*(Nat.choose (m-r) (n-r) : ℂ)) := by
    have hUV : RS16Translation.U t * (1 - C t * X) = 1 := by
      have hh := congrArg (rescale t) (mk_one_mul_one_sub_eq_one (S := ℂ))
      simpa only [RS16Translation.U, map_mul, map_sub, map_one, rescale_X] using hh
    have hpow (r : ℕ) (hr : r ≤ m) : (1 - C t * X)^m*(D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius t)^r = X^r*(1 - C t * X)^(m-r) := by
      dsimp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius]; rw [mul_pow, show m = (m-r)+r by omega, pow_add]
      change (1 - C t * X)^(m-r)*(1 - C t * X)^r*(X^r*RS16Translation.U t^r) = X^r*(1 - C t * X)^(m-r+r-r)
      have hh : (1 - C t * X)^(m-r)*(1 - C t * X)^r*(X^r*RS16Translation.U t^r) = X^r*(1 - C t * X)^(m-r)*(RS16Translation.U t*(1 - C t * X))^r := by rw [mul_pow]; ring
      change (1 - C t * X)^(m-r)*(1 - C t * X)^r*(X^r*RS16Translation.U t^r) = X^r*(1 - C t * X)^(m-r)*(RS16Translation.U t*(1 - C t * X))^r at hh
      rw [hh, hUV, one_pow, mul_one]; simp only [Nat.add_sub_cancel]
    have hV : (1 - C t * X) = rescale (-t) (1+X) := by rw [map_add, map_one, rescale_X, map_neg]; ring
    have hcoeff (a q : ℕ) : coeff q ((1 - C t * X)^a) = (-t)^q*(Nat.choose a q : ℂ) := by
      rw [hV, ← map_pow, coeff_rescale]; congr 1
      have hpoly : ((1+X : PowerSeries ℂ)^a) = (((1+Polynomial.X : Polynomial ℂ)^a) : PowerSeries ℂ) := by simp
      rw [hpoly, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
    rw [RS16Translation.F_translation, local_RS16Series_coeff_mul_subst _ _ _ (by simp [D5.S1.Recurrence.Invariants.CompositionalIterateCongruence.mobius])]; apply sum_congr rfl; intro r hr
    have hrn : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
    rw [hpow r (hrn.trans hnm)]
    have he : n = (n-r)+r := by omega
    conv_lhs => arg 2; arg 1; rw [he]
    rw [coeff_X_pow_mul, hcoeff]
  have local_RS16Series_odd_zero_of_reflection {F : PowerSeries ℂ} (hF : rescale (-1) F = F) (n : ℕ) (hn : Odd n) : coeff n F = 0 := by
    have h := congrArg (coeff n) hF
    rw [coeff_rescale, hn.neg_one_pow] at h; linear_combination -1/2 * h
  have local_RS16Translation_F_half_odd (m n : ℕ) (hn : Odd n) : coeff n (RS16Translation.F m (1/2)) = 0 := by
    have hs0 : constantCoeff (RS16Translation.S m (1/2)) = 0 := by simp [RS16Translation.S]
    have hs : HasSubst (RS16Translation.S m (1/2)) := HasSubst.of_constantCoeff_zero' hs0
    have hSref : rescale (-1) (RS16Translation.S m (1/2)) = RS16Translation.S m (1/2) := by
      ext r; rw [coeff_rescale]
      rcases Nat.even_or_odd r with he | ho
      · rw [he.neg_one_pow, one_mul]
      · have href := Polynomial.bernoulli_eval_one_sub r (1/2)
        have hhalf : (Polynomial.bernoulli r).eval (1/2) = 0 := by norm_num only [show (1:ℚ)-1/2 = 1/2 by norm_num] at href; rw [ho.neg_one_pow] at href; linear_combination 1/2 * href
        have hp : (Polynomial.aeval (1/2 : ℂ)) (Polynomial.bernoulli r) = 0 := by
          have ht : (1/2 : ℂ) = algebraMap ℚ ℂ (1/2 : ℚ) := by norm_num
          rw [Polynomial.aeval_def, ht, Polynomial.eval₂_at_apply, hhalf]; simp
        simp only [RS16Translation.S, coeff_mk]; rw [hp]; simp
    have hFref : rescale (-1) (RS16Translation.F m (1/2)) = RS16Translation.F m (1/2) := by rw [rescale_eq_subst]; unfold RS16Translation.F; rw [subst_comp_subst_apply hs (HasSubst.smul_X' (-1 : ℂ))]; rw [← rescale_eq_subst, hSref]
    exact local_RS16Series_odd_zero_of_reflection hFref n hn
  have hF : RS16Bernoulli.pSeries s2 (-(m : ℂ)) = RS16Translation.F m 0 := by
    unfold RS16Bernoulli.pSeries RS16Translation.F; congr 1; ext n
    by_cases hn : n = 0
    · subst n
      simp [RS16Bernoulli.entrySeries, RS16Translation.S]
    · simp only [coeff_C_mul, coeff_mk, RS16Bernoulli.entrySeries, RS16Translation.S, hn, ↓reduceIte, s2, neg_neg]
      simp only [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_bernoulli, Nat.zero_le, ↓reduceIte, Nat.sub_zero, Nat.choose_zero_right, mul_one]
      have hb : (algebraMap ℚ ℂ) (bernoulli n) = (bernoulli n : ℂ) := by simpa only [Rat.cast_id] using (map_ratCast (algebraMap ℚ ℂ) (bernoulli n))
      simp only [Nat.cast_one, mul_one]; rw [hb]; ring
  have hp (r : ℕ) : p r (-(m : ℂ)) = coeff r (RS16Translation.F m 0) := by change RS16Bernoulli.residuePolynomial r s2 (-(m : ℂ)) = _; rw [local_RS16Bernoulli_p_coefficient, hF]
  unfold annihilates; intro k hkm hk
  let n := m-k
  have hnm : n ≤ m := Nat.sub_le _ _
  have hnodd : Odd n := by rw [Nat.odd_iff] at hk ⊢; rw [Nat.even_iff] at hm; dsimp [n]; omega
  have hz := local_RS16Translation_F_half_odd m n hnodd
  rw [local_RS16Translation_F_coefficient_translation m n hnm (1/2 : ℂ)] at hz; simp_rw [← hp] at hz
  have hfactor : (∑ j ∈ range (m+1), if k ≤ j then (-1 : ℂ)^j * (j ! : ℂ)*p (m-j) (-(m : ℂ))* ((1/2 : ℂ)^(j-k)/((j-k) ! : ℂ)) else 0) = (-1 : ℂ)^k*(k ! : ℂ)* (∑ r ∈ range (n+1), p r (-(m : ℂ))* ((-(1/2 : ℂ))^(n-r)*(Nat.choose (m-r) (n-r) : ℂ))) := by
    classical
    rw [mul_sum]
    apply sum_bij_ne_zero (fun j _ _ => m-j)
    · intro j hj hne
      have hkj : k ≤ j := by by_contra hh; simp [hh] at hne
      simp only [mem_range] at hj ⊢; dsimp [n]; omega
    · intro j hj hne j' hj' hne' he
      simp only [mem_range] at hj hj'; omega
    · intro r hr hne
      refine ⟨m-r, ?_, ?_, ?_⟩
      · simp only [mem_range] at hr ⊢; omega
      · have hrn : r ≤ n := Nat.le_of_lt_succ (mem_range.mp hr)
        have hkj : k ≤ m-r := by dsimp [n] at hrn; omega
        have hj : m-(m-r) = r := by omega
        have hexp : m-r-k = n-r := by dsimp [n]; omega
        simp only [hkj, ↓reduceIte, hj, hexp]; intro hh; apply hne
        have hfac : (k ! : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
        have hjfac : ((m-r) ! : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero (m-r)
        have hp2 : (1/2 : ℂ)^(n-r) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hnf : ((n-r) ! : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero (n-r)
        have hsign : (-1 : ℂ)^(m-r) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hpr : p r (-(m : ℂ)) = 0 := by
          rcases mul_eq_zero.mp hh with hh | hh
          · rcases mul_eq_zero.mp hh with hh | hh
            · exact False.elim ((mul_ne_zero hsign hjfac) hh)
            · exact hh
          · exact False.elim ((div_ne_zero hp2 hnf) hh)
        simp [hpr]
      · simp only [mem_range] at hr
        omega
    · intro j hj hne
      have hkj : k ≤ j := by by_contra hh; simp [hh] at hne
      have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
      have he : n-(m-j) = j-k := by dsimp [n]; omega
      have he' : m-(m-j) = j := by omega
      simp only [hkj, ↓reduceIte, he, he']
      have hchoose : (Nat.choose j (j-k) : ℂ)*(k ! : ℂ)*((j-k) ! : ℂ) = (j ! : ℂ) := by
        have hh := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le j k)
        have hjk : j-(j-k) = k := by omega
        rw [hjk] at hh
        have hh' : (Nat.choose j (j-k) : ℂ)*((j-k) ! : ℂ)*(k ! : ℂ) = (j ! : ℂ) := by exact_mod_cast hh
        linear_combination hh'
      have hqfac : ((j-k) ! : ℂ) ≠ 0 := by exact_mod_cast factorial_ne_zero (j-k)
      have hs : (-1 : ℂ)^j = (-1 : ℂ)^k*(-1 : ℂ)^(j-k) := by rw [← pow_add, Nat.add_sub_of_le hkj]
      rw [hs, neg_pow (1/2 : ℂ) (j-k), ← hchoose]; field_simp <;> ring
  rw [hfactor, hz]; ring
private noncomputable def aPrimary (α : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 1/(4*(Real.sin α : ℂ)^2) else -(Complex.I*(Real.cos (2*α)/Real.sin (2*α) : ℂ))^(if Even n then 1 else 0) / (n ! : ℂ)*negativePolylog n (Complex.exp (2*α*Complex.I))
end LogLaplacianEvenResidueVanishing
namespace LogLaplacianEvenResidueVanishing
open PowerSeries
private lemma primary_square_inverse (α : ℝ) (hα : 0 < α) (hπα : α < Real.pi) (hne : α ≠ Real.pi/2) : (mk (c α))^2 * (1-C (2*(Real.cos (2*α) : ℂ))*RS16Series.expScale (-1)+RS16Series.expScale (-2)) = 1 := by
  have local_RS16Series_coeff_mul_subst (F G V : PowerSeries ℂ) (hG : constantCoeff G = 0) (n : ℕ) : coeff n (V * F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff n (V * G^r) := by
    have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    classical
    have hg : HasSubst G := HasSubst.of_constantCoeff_zero' hG
    have hex (q : ℕ) (hq : q ≤ n) : coeff q (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff q (G^r) := by
      rw [coeff_subst' hg]; apply finsum_eq_sum_of_support_subset; intro r hr
      by_contra hnr
      have hnr' : n < r := by simp only [Finset.mem_coe, mem_range] at hnr; omega
      have hz : coeff q (G^r) = 0 := by apply coeff_of_lt_order; exact lt_of_lt_of_le (by exact_mod_cast (lt_of_le_of_lt hq hnr')) (le_order_pow_of_constantCoeff_eq_zero r hG)
      exact hr (by simp [hz])
    rw [local_RS16Series_coeff_product]
    have hterms : ∀ q ∈ range (n+1), coeff (n-q) (F.subst G) = ∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r) := by intro q hq; exact hex _ (Nat.sub_le _ _)
    have hs : (∑ q ∈ range (n+1), coeff q V * coeff (n-q) (F.subst G)) = ∑ q ∈ range (n+1), coeff q V * (∑ r ∈ range (n+1), coeff r F * coeff (n-q) (G^r)) := by apply sum_congr rfl; intro q hq; rw [hterms q hq]
    rw [hs]; simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro r hr; rw [local_RS16Series_coeff_product, mul_sum]; apply sum_congr rfl; intro q hq; ring
  have local_T_stirling (n q : ℕ) : coeff n (RS16ExpStirling.T^q) =
      (q ! : ℂ) * (Nat.stirlingSecond n q : ℂ) / (n ! : ℂ) := by
    have hi := congrArg (Int.castRingHom ℂ)
      (D5.S1.Recurrence.Parity.StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion n q)
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at hi
    have hterm (j : ℕ) :
        coeff n ((exp ℂ)^j * (-1 : PowerSeries ℂ)^(q-j) * (Nat.choose q j : PowerSeries ℂ)) =
          (-1 : ℂ)^(q-j) * (Nat.choose q j : ℂ) * (j : ℂ)^n / (n ! : ℂ) := by
      have hneg : (-1 : PowerSeries ℂ)^(q-j) = C ((-1 : ℂ)^(q-j)) := by simp
      have hchoose : (Nat.choose q j : PowerSeries ℂ) = C (Nat.choose q j : ℂ) := by simp
      rw [hneg, hchoose, coeff_mul_C, coeff_mul_C, exp_pow_eq_rescale_exp,
        coeff_rescale, coeff_exp]
      simp [div_eq_mul_inv]
      ring
    simp only [RS16ExpStirling.T, RS16Series.expScale, rescale_one, RingHom.id_apply,
      sub_eq_add_neg, add_pow, map_sum]
    simp_rw [hterm]
    rw [← sum_div, ← hi]
  have local_RS16PolylogGF_G_coeff (n : ℕ) (z : ℂ) (hz : z ≠ 1) : coeff n (RS16PolylogGF.G z) = LogLaplacianEvenResidueVanishing.negativePolylog n z/(n ! : ℂ) := by
    have hv : constantCoeff (RS16PolylogGF.V z) = 0 := by simp [RS16PolylogGF.V, RS16ExpStirling.T, RS16Series.expScale]
    have hvpow (q : ℕ) : (RS16PolylogGF.V z)^q = C ((z/(1-z))^q)*RS16ExpStirling.T^q := by simp only [RS16PolylogGF.V, mul_pow, map_pow]
    have hs := local_RS16Series_coeff_mul_subst (mk (1 : ℕ → ℂ)) (RS16PolylogGF.V z) 1 hv n
    simp only [one_mul, coeff_mk, Pi.one_apply] at hs; simp_rw [hvpow, coeff_C_mul, local_T_stirling] at hs; rw [RS16PolylogGF.G, map_sub, RS16PolylogGF.fullG, coeff_C_mul, hs, RS16Polylog.negativePolylog_finite n z hz]
    have ht (q : ℕ) : 1/(1-z)*((z/(1-z))^q*((q ! : ℂ)*(Nat.stirlingSecond n q : ℂ)/(n ! : ℂ))) = ((Nat.stirlingSecond n q : ℂ)*(q ! : ℂ)*RS16Polylog.R q z)/(n ! : ℂ) := by unfold RS16Polylog.R; rw [div_pow, pow_succ]; field_simp <;> ring
    rw [mul_sum]; simp_rw [ht]; rw [← sum_div, RS16Polylog.finiteLi]; rw [sub_div]; congr 1
    by_cases hn : n = 0
    · subst n; simp
    · simp [hn, coeff_one]
  have local_RS16_primary_square_coefficients (α : ℝ) (hα : 0 < α) (hπα : α < Real.pi) (hne : α ≠ Real.pi/2) : (mk (LogLaplacianEvenResidueVanishing.c α))^2 = mk (LogLaplacianEvenResidueVanishing.aPrimary α) := by
    classical
    have hsin : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπα).ne'
    ext n; rw [pow_two, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]; simp only [coeff_mk]
    cases n with
    | zero => simp [LogLaplacianEvenResidueVanishing.aPrimary, LogLaplacianEvenResidueVanishing.c]; field_simp; ring
    | succ j =>
      have hrec : LogLaplacianEvenResidueVanishing.c α (j+1) = (Real.sin α : ℂ)* (LogLaplacianEvenResidueVanishing.aPrimary α (j+1) - ∑ q : Fin j, LogLaplacianEvenResidueVanishing.c α (q.val+1)*LogLaplacianEvenResidueVanishing.c α (j-q.val)) := by rw [LogLaplacianEvenResidueVanishing.c, if_neg hne]; simp only [LogLaplacianEvenResidueVanishing.aPrimary, Nat.succ_ne_zero, ↓reduceIte]
      have hsum : (∑ q ∈ range (j+2), LogLaplacianEvenResidueVanishing.c α q * LogLaplacianEvenResidueVanishing.c α (j+1-q)) = (∑ q : Fin j, LogLaplacianEvenResidueVanishing.c α (q.val+1)*LogLaplacianEvenResidueVanishing.c α (j-q.val)) + LogLaplacianEvenResidueVanishing.c α (j+1)*LogLaplacianEvenResidueVanishing.c α 0 + LogLaplacianEvenResidueVanishing.c α 0*LogLaplacianEvenResidueVanishing.c α (j+1) := by
        rw [sum_range_succ', sum_range_succ]; simp only [Nat.add_sub_add_right, Nat.sub_self, Nat.sub_zero]; congr 2
        exact (Fin.sum_univ_eq_sum_range (fun q => LogLaplacianEvenResidueVanishing.c α (q+1)*LogLaplacianEvenResidueVanishing.c α (j-q)) j).symm
      have h0 : LogLaplacianEvenResidueVanishing.c α 0 = 1/(2*(Real.sin α : ℂ)) := by rw [LogLaplacianEvenResidueVanishing.c]
      rw [hsum, hrec, h0]; field_simp; ring
  have local_RS16PolylogGF_quad_coeff_pos (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : z ≠ 1) : coeff n (RS16PolylogGF.quad z) = ((z*(-1 : ℂ)^n+z⁻¹)/(z-z⁻¹)) * (LogLaplacianEvenResidueVanishing.negativePolylog n z/(n ! : ℂ)) := by
    have hf : coeff n (RS16PolylogGF.fullG z) = LogLaplacianEvenResidueVanishing.negativePolylog n z/(n ! : ℂ) := by
      have hh := local_RS16PolylogGF_G_coeff n z hz
      simpa only [RS16PolylogGF.G, map_sub, coeff_one, hn, ↓reduceIte, sub_zero] using hh
    simp only [RS16PolylogGF.quad, map_sub, coeff_C_mul, coeff_rescale, coeff_one, hn, ↓reduceIte, hf]; ring
  have local_RS16PolylogGF_fullG_inverse (z : ℂ) (hz : z ≠ 1) : RS16PolylogGF.fullG z * (1-C z*RS16Series.expScale 1) = 1 := by
    have hv : constantCoeff (RS16PolylogGF.V z) = 0 := by simp [RS16PolylogGF.V, RS16ExpStirling.T, RS16Series.expScale]
    have hs := HasSubst.of_constantCoeff_zero' hv
    have hh := congrArg (fun F : PowerSeries ℂ => F.subst (RS16PolylogGF.V z)) (mk_one_mul_one_sub_eq_one ℂ)
    rw [subst_mul hs, subst_sub hs, subst_X hs] at hh
    have hOne : (1 : PowerSeries ℂ).subst (RS16PolylogGF.V z) = 1 := by change (C (1 : ℂ)).subst (RS16PolylogGF.V z) = 1; rw [subst_C]; simp
    rw [hOne] at hh
    have hd : 1-C z*RS16Series.expScale 1 = C (1-z)*(1-RS16PolylogGF.V z) := by
      unfold RS16PolylogGF.V RS16ExpStirling.T
      have he : (1-z)*(z/(1-z)) = z := by field_simp
      simp only [mul_sub, ← mul_assoc, ← map_mul]; rw [he]; simp only [map_sub, map_one]; ring
    rw [RS16PolylogGF.fullG, hd]
    calc
      _ = C ((1/(1-z))*(1-z))*((mk (1 : ℕ → ℂ)).subst (RS16PolylogGF.V z)*(1-RS16PolylogGF.V z)) := by rw [map_mul]; ring
      _ = 1 := by rw [hh, one_div, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hz)), map_one, mul_one]
  have local_RS16Series_coeff_expScale (t : ℂ) (n : ℕ) : coeff n (RS16Series.expScale t) = t^n / (n ! : ℂ) := by simp [RS16Series.expScale, coeff_rescale, div_eq_mul_inv]
  have local_RS16Series_reflect_expScale (t : ℂ) : rescale (-1) (RS16Series.expScale t) = RS16Series.expScale (-t) := by ext n; simp only [coeff_rescale, local_RS16Series_coeff_expScale]; rw [neg_pow]; ring
  have local_RS16PolylogGF_quad_inverse (z : ℂ) (hz : z ≠ 1) (hz0 : z ≠ 0) (hd : z-z⁻¹ ≠ 0) : RS16PolylogGF.quad z*(1-C (z+z⁻¹)*RS16Series.expScale (-1)+RS16Series.expScale (-2)) = 1 := by
    let E := RS16Series.expScale 1
    let M := RS16Series.expScale (-1)
    have he : E*M = 1 := by dsimp [E, M]; rw [RS16Series.expScale, RS16Series.expScale, exp_mul_exp_eq_exp_add]; norm_num
    have hm : M*M = RS16Series.expScale (-2) := by dsimp [M]; rw [RS16Series.expScale, RS16Series.expScale, exp_mul_exp_eq_exp_add]; norm_num
    have hF : RS16PolylogGF.fullG z*(1-C z*E) = 1 := local_RS16PolylogGF_fullG_inverse z hz
    have hU : rescale (-1) (RS16PolylogGF.fullG z)*(1-C z*M) = 1 := by
      have hh := congrArg (rescale (-1 : ℂ)) hF
      have hc : rescale (-1) (C z) = C z := by ext n; by_cases hn : n = 0 <;> simp [coeff_rescale, coeff_C, hn]
      simpa only [map_mul, map_sub, map_one, hc, local_RS16Series_reflect_expScale, neg_one_mul, E, M] using hh
    have hu : C z⁻¹*M*(C z*E) = 1 := by
      calc
        _ = C (z⁻¹*z)*(E*M) := by rw [map_mul]; ring
        _ = 1 := by rw [inv_mul_cancel₀ hz0, map_one, he, one_mul]
    have hW : (1-RS16PolylogGF.fullG z)*(1-C z⁻¹*M) = 1 := by
      calc
        _ = 1-C z⁻¹*M + C z⁻¹*M*(RS16PolylogGF.fullG z*(1-C z*E)) := by linear_combination RS16PolylogGF.fullG z * hu
        _ = 1 := by rw [hF]; ring
    have hden : 1-C (z+z⁻¹)*M+RS16Series.expScale (-2) = (1-C z*M)*(1-C z⁻¹*M) := by
      have hc : C z*C z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
      rw [map_add, ← hm]; linear_combination -(M*M)*hc
    rw [RS16PolylogGF.quad, hden]
    calc
      _ = C (z/(z-z⁻¹))*(rescale (-1) (RS16PolylogGF.fullG z)*(1-C z*M))*(1-C z⁻¹*M) - C (z⁻¹/(z-z⁻¹))*((1-RS16PolylogGF.fullG z)*(1-C z⁻¹*M))*(1-C z*M) := by ring
      _ = C (1/(z-z⁻¹))*(C z*(1-C z⁻¹*M)-C z⁻¹*(1-C z*M)) := by rw [hU, hW]; simp only [mul_one, div_eq_mul_inv, map_mul, map_one]; ring
      _ = 1 := by
        have hnum : C z*(1-C z⁻¹*M)-C z⁻¹*(1-C z*M) = C (z-z⁻¹) := by rw [map_sub]; ring
        rw [hnum, ← map_mul, one_div, inv_mul_cancel₀ hd, map_one]
  let z : ℂ := Complex.exp (2*α*Complex.I)
  have hsα : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα hπα).ne'
  have hcα : Real.cos α ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩).ne'
    · exact (Real.cos_neg_of_pi_div_two_lt_of_lt hgt (by linarith [Real.pi_pos])).ne
  have hs2 : (Real.sin (2*α) : ℂ) ≠ 0 := by exact_mod_cast (by rw [Real.sin_two_mul]; exact mul_ne_zero (mul_ne_zero (by norm_num) hsα) hcα : Real.sin (2*α) ≠ 0)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hz : z = (Real.cos (2*α) : ℂ)+(Real.sin (2*α) : ℂ)*Complex.I := by
    dsimp [z]
    convert Complex.exp_ofReal_mul_I (2*α) using 1 <;> push_cast <;> rfl
  have hzi : z⁻¹ = (Real.cos (2*α) : ℂ)-(Real.sin (2*α) : ℂ)*Complex.I := by
    dsimp [z]; rw [← Complex.exp_neg]
    have he : -(2*(α:ℂ)*Complex.I) = ((-(2*α):ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [he, Complex.exp_ofReal_mul_I]; simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]; ring
  have hsum : z+z⁻¹ = 2*(Real.cos (2*α) : ℂ) := by rw [hzi, hz]; ring
  have hdelta : z-z⁻¹ = 2*(Real.sin (2*α) : ℂ)*Complex.I := by rw [hzi, hz]; ring
  have hd : z-z⁻¹ ≠ 0 := by rw [hdelta]; exact mul_ne_zero (mul_ne_zero (by norm_num) hs2) Complex.I_ne_zero
  have hz1 : z ≠ 1 := by
    intro he
    have hii : z⁻¹ = 1 := by rw [he, inv_one]
    exact hd (by simp [he])
  have hq := local_RS16PolylogGF_quad_inverse z hz1 hz0 hd
  rw [hsum] at hq
  have hcoeff : mk (aPrimary α) = RS16PolylogGF.quad z := by
    ext n; rw [coeff_mk]
    by_cases hn : n = 0
    · subst n
      have hq0 := congrArg constantCoeff hq
      simp only [map_mul, map_add, map_sub, map_one, constantCoeff_C] at hq0
      have he0 (t : ℂ) : constantCoeff (RS16Series.expScale t) = 1 := by rw [← coeff_zero_eq_constantCoeff_apply, local_RS16Series_coeff_expScale]; simp
      simp only [he0, mul_one] at hq0
      have hden : (1-2*(Real.cos (2*α) : ℂ)+1) = 4*(Real.sin α : ℂ)^2 := by
        have hr : (1-2*Real.cos (2*α)+1) = 4*(Real.sin α)^2 := by rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq α]
        exact_mod_cast hr
      rw [hden] at hq0
      have hsn : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast hsα
      unfold aPrimary; simp only [↓reduceIte]; apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ hsn))).mpr; simpa only [coeff_zero_eq_constantCoeff] using hq0.symm
    · rw [local_RS16PolylogGF_quad_coeff_pos n hn z hz1]
      simp only [aPrimary, hn, ↓reduceIte]
      have hl : LogLaplacianEvenResidueVanishing.negativePolylog n z = negativePolylog n z := rfl
      rw [hl]; change -(Complex.I * (Real.cos (2*α)/Real.sin (2*α) : ℂ))^(if Even n then 1 else 0) / (n ! : ℂ)*negativePolylog n z = ((z*(-1 : ℂ)^n+z⁻¹)/(z-z⁻¹))*(negativePolylog n z/(n ! : ℂ))
      by_cases he : Even n
      · rw [he.neg_one_pow]
        simp only [he, ↓reduceIte, pow_one, mul_one]
        have hfrac : (z+z⁻¹)/(z-z⁻¹) = -Complex.I*(Real.cos (2*α)/Real.sin (2*α) : ℂ) := by rw [hsum, hdelta]; field_simp; simp [Complex.I_sq]
        rw [hfrac]; ring
      · have ho : Odd n := Nat.not_even_iff_odd.mp he
        rw [ho.neg_one_pow]; simp only [he, ↓reduceIte, pow_zero]
        have hfrac : (z*(-1)+z⁻¹)/(z-z⁻¹) = -1 := by
          calc
            _ = -(z-z⁻¹)/(z-z⁻¹) := by congr 1; ring
            _ = -1 := neg_div_self hd
        rw [hfrac]; ring
  rw [local_RS16_primary_square_coefficients α hα hπα hne, hcoeff]; exact hq
theorem result : claim := by
  have local_RS16Series_centered_square_even (Cseries : PowerSeries ℂ) (z : ℂ) (hc : constantCoeff Cseries ≠ 0) (hsq : Cseries^2 * (1 - C (2*z) * RS16Series.expScale (-1) + RS16Series.expScale (-2)) = 1) : ∀ n, Odd n → coeff n (RS16Series.expScale (-1/2) * Cseries) = 0 := by
    have local_RS16Series_coeff_expScale (t : ℂ) (n : ℕ) : coeff n (RS16Series.expScale t) = t^n / (n ! : ℂ) := by simp [RS16Series.expScale, coeff_rescale, div_eq_mul_inv]
    have local_RS16Series_odd_zero_of_reflection {F : PowerSeries ℂ} (hF : rescale (-1) F = F) (n : ℕ) (hn : Odd n) : coeff n F = 0 := by
      have h := congrArg (coeff n) hF
      rw [coeff_rescale, hn.neg_one_pow] at h; linear_combination -1/2 * h
    have local_RS16Series_reflect_expScale (t : ℂ) : rescale (-1) (RS16Series.expScale t) = RS16Series.expScale (-t) := by ext n; simp only [coeff_rescale, local_RS16Series_coeff_expScale]; rw [neg_pow]; ring
    have local_RS16Series_reflection_of_square {F : PowerSeries ℂ} (hsq : rescale (-1) (F^2) = F^2) (hc : constantCoeff F ≠ 0) : rescale (-1) F = F := by
      rw [map_pow] at hsq
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
      · exact h
      · have h0 := congrArg constantCoeff h
        change constantCoeff (rescale (-1) F) = -constantCoeff F at h0
        have hr : constantCoeff (rescale (-1) F) = constantCoeff F := by simp only [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul]
        rw [hr] at h0; exact False.elim (hc (by linear_combination 1/2 * h0))
    let H := RS16Series.expScale (-1/2) * Cseries
    let D := RS16Series.expScale 1 + RS16Series.expScale (-1) - C (2*z)
    have he (a b : ℂ) : RS16Series.expScale a * RS16Series.expScale b = RS16Series.expScale (a+b) :=
      exp_mul_exp_eq_exp_add a b
    have hD : RS16Series.expScale (-1) * D = 1 - C (2*z) * RS16Series.expScale (-1) + RS16Series.expScale (-2) := by dsimp [D]; rw [mul_sub, mul_add, he, he]; norm_num [RS16Series.expScale]; ring
    have hH : H^2 * D = 1 := by
      dsimp [H]; rw [mul_pow, pow_two (RS16Series.expScale (-1/2)), he]; norm_num
      calc
        RS16Series.expScale (-1) * Cseries ^ 2 * D = Cseries^2 * (RS16Series.expScale (-1)*D) := by ring
        _ = 1 := by rw [hD, hsq]
    have hrC (a : ℂ) : rescale (-1) (C a) = C a := by
      ext n
      by_cases hn : n = 0 <;> simp [coeff_rescale, coeff_C, hn]
    have hDref : rescale (-1) D = D := by dsimp [D]; simp only [map_sub, map_add, local_RS16Series_reflect_expScale, hrC]; norm_num; ring
    have hDne : D ≠ 0 := by intro hz; rw [hz, mul_zero] at hH; exact zero_ne_one hH
    have hsqH : rescale (-1) (H^2) = H^2 := by
      have hr := congrArg (rescale (-1 : ℂ)) hH
      rw [map_mul, hDref, map_one] at hr; exact mul_right_cancel₀ hDne (hr.trans hH.symm)
    have hHc : constantCoeff H ≠ 0 := by
      dsimp [H]; rw [map_mul]
      have he0 : constantCoeff (RS16Series.expScale (-1/2)) = 1 := by rw [← coeff_zero_eq_constantCoeff_apply, local_RS16Series_coeff_expScale]; norm_num
      rwa [he0, one_mul]
    exact fun n hn => local_RS16Series_odd_zero_of_reflection (local_RS16Series_reflection_of_square hsqH hHc) n hn
  have local_RS16Convolution_A_grouped (d : ℕ → ℕ → ℂ) (c w : ℕ → ℂ) (l : ℕ) : RS16Convolution.weightedConvolution d c w l = ∑ t ∈ range (l/2+1), (∑ k ∈ range (t+1), w k * d t k) * c (l-2*t) := by
    classical
    unfold RS16Convolution.weightedConvolution RS16Convolution.coefficientConvolution; simp_rw [mul_sum]
    have hrows : ∀ k ∈ range (l/2+1), (∑ j ∈ range ((l-2*k)/2+1), w k * (d (k+j) k * c (l-2*k-2*j))) = ∑ t ∈ Ico k (l/2+1), w k * d t k * c (l-2*t) := by
      intro k hk
      have hkl : k ≤ l/2 := by simp only [mem_range] at hk; omega
      apply sum_bij (fun j _ => k+j)
      · intro j hj
        simp only [mem_range] at hj; simp only [mem_Ico]; omega
      · intro j hj j' hj' he; omega
      · intro t ht
        simp only [mem_Ico] at ht
        refine ⟨t-k, ?_, by omega⟩
        simp only [mem_range]; omega
      · intro j hj
        have he : l-2*k-2*j = l-2*(k+j) := by omega
        rw [he]; ring
    have hmiddle : (∑ k ∈ range (l/2+1), ∑ j ∈ range ((l-2*k)/2+1), w k * (d (k+j) k * c (l-2*k-2*j))) = ∑ k ∈ Ico 0 (l/2+1), ∑ t ∈ Ico k (l/2+1), w k * d t k * c (l-2*t) := by rw [Nat.Ico_zero_eq_range]; exact sum_congr rfl hrows
    rw [hmiddle, sum_Ico_Ico_comm]; simp only [Nat.Ico_zero_eq_range, sum_mul]
  have local_RS16Convolution_A_coeff_product (d : ℕ → ℕ → ℂ) (c w : ℕ → ℂ) (l : ℕ) : RS16Convolution.weightedConvolution d c w l = PowerSeries.coeff l (PowerSeries.mk c * PowerSeries.mk (RS16Convolution.E d w)) := by
    classical
    rw [mul_comm, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]; simp only [PowerSeries.coeff_mk]; rw [local_RS16Convolution_A_grouped]; symm
    apply sum_bij_ne_zero (fun q _ _ => q/2)
    · intro q hq hne
      simp only [mem_range] at hq ⊢; omega
    · intro q hq hne q' hq' hne' hdiv
      have hqeven : Even q := by
        by_contra ho
        simp [RS16Convolution.E, ho] at hne
      have hq'even : Even q' := by
        by_contra ho
        simp [RS16Convolution.E, ho] at hne'
      rw [Nat.even_iff] at hqeven hq'even; omega
    · intro t ht hne
      refine ⟨2*t, ?_, ?_, by omega⟩
      · simp only [mem_range] at ht ⊢
        omega
      · simpa [RS16Convolution.E, even_two_mul, Nat.mul_div_cancel_left] using hne
    · intro q hq hne
      have hqeven : Even q := by
        by_contra ho
        simp [RS16Convolution.E, ho] at hne
      have he : 2*(q/2) = q := by rw [Nat.even_iff] at hqeven; omega
      simp [RS16Convolution.E, hqeven, he]
  have local_odd_convolution_zero (m : ℕ) (α : ℝ) (hann : LogLaplacianEvenResidueVanishing.annihilates m) (hbridge : ∀ j ≤ m, LogLaplacianEvenResidueVanishing.derivativeArray α j = ∑ k ∈ range (m + 1), if k ≤ j ∧ Odd k then (k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0) : ∑ j ∈ range (m + 1), (-1 : ℂ)^j * (j ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-j) (-m) * LogLaplacianEvenResidueVanishing.derivativeArray α j = 0 := by
    classical
    have hb : ∀ j ∈ range (m+1), LogLaplacianEvenResidueVanishing.derivativeArray α j = ∑ k ∈ range (m + 1), if k ≤ j ∧ Odd k then (k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0 := by intro j hj; exact hbridge j (Nat.le_of_lt_succ (mem_range.mp hj))
    calc
      (∑ j ∈ range (m + 1), (-1 : ℂ)^j * (j ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-j) (-m) * LogLaplacianEvenResidueVanishing.derivativeArray α j) = ∑ j ∈ range (m + 1), (-1 : ℂ)^j * (j ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-j) (-m) * (∑ k ∈ range (m + 1), if k ≤ j ∧ Odd k then (k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0) := by apply Finset.sum_congr rfl; intro j hj; rw [hb j hj]
      _ = 0 := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro k hk
        by_cases hok : Odd k
        · have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
          have hh := hann k hkm hok
          simp only [hok, and_true]
          calc
            (∑ x ∈ range (m + 1), (-1 : ℂ)^x * (x ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-x) (-m) * (if k ≤ x then (k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1) * ((1/2 : ℂ)^(x-k) / ((x-k) ! : ℂ)) else 0)) = ∑ x ∈ range (m + 1), ((k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1)) * (if k ≤ x then (-1 : ℂ)^x * (x ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-x) (-m) * ((1/2 : ℂ)^(x-k) / ((x-k) ! : ℂ)) else 0) := by
                  apply Finset.sum_congr rfl; intro x hx
                  by_cases hkx : k ≤ x <;> simp [hkx] <;> ring
            _ = ((k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1)) * (∑ x ∈ range (m + 1), if k ≤ x then (-1 : ℂ)^x * (x ! : ℂ) * LogLaplacianEvenResidueVanishing.p (m-x) (-m) * ((1/2 : ℂ)^(x-k) / ((x-k) ! : ℂ)) else 0) := by rw [Finset.mul_sum]
            _ = ((k + 1 : ℂ) * LogLaplacianEvenResidueVanishing.shifted α (k+1)) * 0 := by rw [hh]
            _ = 0 := mul_zero _
        · simp [hok]
  have local_center_logistic : RS16Center.center * (1+rescale (-1) (exp ℚ)) = 1 := by
    have hb : bernoulliPowerSeries ℚ * (exp ℚ-1) = X :=
      bernoulliPowerSeries_mul_exp_sub_one ℚ
    have hb2 : rescale 2 (bernoulliPowerSeries ℚ) * (rescale 2 (exp ℚ)-1) = 2 * X := by
      have hh := congrArg (rescale (2 : ℚ)) hb
      simpa only [map_mul, map_sub, map_one, rescale_X, map_ofNat] using hh
    have he2 : rescale (2 : ℚ) (exp ℚ) = exp ℚ * exp ℚ := by simpa [pow_two] using (exp_pow_eq_rescale_exp (A := ℚ) 2).symm
    have hEne : exp ℚ - 1 ≠ 0 := by
      intro h
      have hz := congrArg (coeff 1) h
      norm_num at hz
    have hdiff : (rescale 2 (bernoulliPowerSeries ℚ) - (bernoulliPowerSeries ℚ)) * (exp ℚ+1) = -X := by
      apply mul_right_cancel₀ hEne
      calc
        (rescale 2 (bernoulliPowerSeries ℚ) - (bernoulliPowerSeries ℚ)) * (exp ℚ+1) * (exp ℚ-1) = rescale 2 (bernoulliPowerSeries ℚ) * (rescale 2 (exp ℚ)-1) - (bernoulliPowerSeries ℚ) * (exp ℚ-1) * (exp ℚ+1) := by rw [he2]; ring
        _ = 2*X - X*(exp ℚ+1) := by rw [hb2, hb]
        _ = -X * (exp ℚ-1) := by ring
    have hC : X * RS16Center.center = X + rescale 2 (bernoulliPowerSeries ℚ) - (bernoulliPowerSeries ℚ) := by
      ext n
      cases n with
      | zero => simp only [coeff_zero_X_mul, map_sub, map_add, coeff_zero_X, coeff_rescale, pow_zero, one_mul]; simp [bernoulliPowerSeries]
      | succ n =>
        rw [coeff_succ_X_mul]; simp only [RS16Center.center, coeff_mk, map_sub, map_add, coeff_X, coeff_rescale, bernoulliPowerSeries, map_div₀, map_natCast, Algebra.algebraMap_self, RingHom.id_apply]
        by_cases hn : n = 0
        · subst n
          norm_num [bernoulli_one]
        · simp only [hn, ↓reduceIte]
          have hn1 : n+1 ≠ 1 := by omega
          rw [if_neg hn1]; ring
    have hCE : RS16Center.center * (exp ℚ+1) = exp ℚ := by
      apply X_mul_cancel
      calc
        X * (RS16Center.center*(exp ℚ+1)) = (X+rescale 2 (bernoulliPowerSeries ℚ)-(bernoulliPowerSeries ℚ)) * (exp ℚ+1) := by rw [← mul_assoc, hC]
        _ = X*(exp ℚ+1)+(rescale 2 (bernoulliPowerSeries ℚ)-(bernoulliPowerSeries ℚ))*(exp ℚ+1) := by ring
        _ = X*exp ℚ := by rw [hdiff]; ring
    have hneg : exp ℚ * rescale (-1) (exp ℚ) = 1 := by simpa [evalNegHom] using (exp_mul_exp_neg_eq_one (A := ℚ))
    calc
      RS16Center.center * (1+rescale (-1) (exp ℚ)) = (RS16Center.center * (exp ℚ+1)) * rescale (-1) (exp ℚ) := by rw [mul_assoc, add_mul, hneg, one_mul]
      _ = 1 := by rw [hCE, hneg]
  have local_shifted_A_odd (d : ℕ → ℕ → ℂ) (c w : ℕ → ℂ) (hc : ∀ n, Odd n → coeff n (rescale (-1/2) (exp ℂ) * mk c) = 0) : ∀ n, Odd n → coeff n (rescale (-1/2) (exp ℂ) * mk (RS16Convolution.weightedConvolution d c w)) = 0 := by
    have hA : mk (RS16Convolution.weightedConvolution d c w) = mk c * mk (RS16Convolution.E d w) := by ext n; simp only [coeff_mk]; exact local_RS16Convolution_A_coeff_product d c w n
    rw [hA, ← mul_assoc]; intro n hn; rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]; apply sum_eq_zero; intro q hq
    by_cases hqo : Odd q
    · rw [hc q hqo, zero_mul]
    · have hno : Odd (n-q) := by
        simp only [mem_range] at hq; rw [Nat.odd_iff] at hn ⊢; rw [Nat.odd_iff] at hqo; omega
      have hne : ¬Even (n-q) := Nat.not_even_iff_odd.mpr hno
      simp [RS16Convolution.E, hne]
  have local_derivative_coeff_reconstruction (a : ℕ → ℂ) (h : ∀ n, Odd n → coeff n (RS16Series.expScale (-1/2) * PowerSeries.mk a) = 0) (j : ℕ) : (j+1 : ℂ) * a (j+1) - (1/2 : ℂ) * a j = ∑ k ∈ range (j+1), if Odd k then (k+1 : ℂ) * coeff (k+1) (RS16Series.expScale (-1/2) * PowerSeries.mk a) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0 := by
    have local_RS16Series_coeff_expScale (t : ℂ) (n : ℕ) : coeff n (RS16Series.expScale t) = t^n / (n ! : ℂ) := by simp [RS16Series.expScale, coeff_rescale, div_eq_mul_inv]
    have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have local_RS16Series_coeff_product_right (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff (n-q) f * coeff q g := by rw [mul_comm, local_RS16Series_coeff_product]; apply sum_congr rfl; intro q hq; ring
    have local_RS16Series_derivative_expScale (t : ℂ) : PowerSeries.derivative ℂ (RS16Series.expScale t) = C t * RS16Series.expScale t := by
      ext n; rw [coeff_derivative, coeff_C_mul, local_RS16Series_coeff_expScale, local_RS16Series_coeff_expScale]; simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp
    have local_RS16Series_reconstruct (F : PowerSeries ℂ) : F = RS16Series.expScale (1/2) * (RS16Series.expScale (-1/2) * F) := by
      rw [← mul_assoc]
      have h : RS16Series.expScale (1/2) * RS16Series.expScale (-1/2) = 1 := by rw [RS16Series.expScale, RS16Series.expScale, exp_mul_exp_eq_exp_add]; norm_num
      rw [h, one_mul]
    have local_RS16Series_derivative_reconstruct (F : PowerSeries ℂ) : PowerSeries.derivative ℂ F - C (1/2) * F = RS16Series.expScale (1/2) * PowerSeries.derivative ℂ (RS16Series.expScale (-1/2) * F) := by
      have hrec := local_RS16Series_reconstruct F
      conv_lhs => lhs; rw [hrec]
      rw [Derivation.leibniz, local_RS16Series_derivative_expScale]; simp only [smul_eq_mul]
      conv_lhs => rhs; rw [hrec]
      ring
    have hd := congrArg (coeff j) (local_RS16Series_derivative_reconstruct (PowerSeries.mk a))
    simp only [map_sub, coeff_derivative, coeff_C_mul, PowerSeries.mk, coeff_mk] at hd; rw [mul_comm (j+1 : ℂ) (a (j+1)), hd, local_RS16Series_coeff_product_right]; apply sum_congr rfl; intro k hk; rw [coeff_derivative, local_RS16Series_coeff_expScale]
    by_cases ho : Odd k
    · simp only [ho, ↓reduceIte]
      ring
    · have ho' : Odd (k+1) := by
        rw [Nat.odd_iff] at ho ⊢; omega
      simp [ho, h (k+1) ho']
  have local_RS16_sum_shift_Icc (m : ℕ) (F : ℕ → ℂ) : (∑ ell ∈ Icc 1 (m+1), F ell) = ∑ j ∈ range (m+1), F (j+1) := by
    apply Finset.sum_bij (fun ell _ => ell - 1)
    · intro ell hell
      simp only [mem_Icc] at hell; simp only [mem_range]; omega
    · intro a ha b hb hab
      simp only [mem_Icc] at ha hb; omega
    · intro j hj
      simp only [mem_range] at hj
      refine ⟨j+1, ?_, ?_⟩
      · simp only [mem_Icc]
        omega
      · omega
    · intro ell hell
      simp only [mem_Icc] at hell; simpa [Nat.sub_add_cancel hell.1]
  have local_RS16_paper_to_derivative (m : ℕ) (α : ℝ) : paperBracket m α = -∑ j ∈ range (m + 1), (-1 : ℂ)^j * (j ! : ℂ) * p (m-j) (-m) * derivativeArray α j := by
    unfold paperBracket derivativeArray; rw [local_RS16_sum_shift_Icc]; simp_rw [Nat.add_sub_add_right]; simp_rw [mul_sub]; simp_rw [Finset.sum_sub_distrib]; simp_rw [Nat.factorial_succ]; push_cast; simp_rw [pow_succ, neg_sub]; simp_rw [sub_eq_add_neg]
    rw [← Finset.sum_neg_distrib]
    have hterm (x : ℕ) : (-1 : ℂ)^x * (-1) * ((x+1 : ℂ) * (x ! : ℂ)) * p (m-x) (-m) * A α (x+1) = -((-1 : ℂ)^x * (x ! : ℂ) * p (m-x) (-m) * ((x+1 : ℂ) * A α (x+1))) := by push_cast; ring
    simp_rw [hterm]; rw [Finset.mul_sum]; ring
  have local_RS16Series_coeff_expScale (t : ℂ) (n : ℕ) : coeff n (RS16Series.expScale t) = t^n / (n ! : ℂ) := by simp [RS16Series.expScale, coeff_rescale, div_eq_mul_inv]
  have local_RS16_center_primary_square : (mk (LogLaplacianEvenResidueVanishing.c (Real.pi/2)))^2 * (1-C (2*(Real.cos (2*(Real.pi/2)) : ℂ))*RS16Series.expScale (-1)+RS16Series.expScale (-2)) = 1 := by
    have hc : mk (LogLaplacianEvenResidueVanishing.c (Real.pi/2)) = PowerSeries.map (algebraMap ℚ ℂ) RS16Center.center := by
      ext n; rw [coeff_mk, coeff_map]
      cases n with
      | zero => simp [LogLaplacianEvenResidueVanishing.c, RS16Center.center, Real.sin_pi_div_two]
      | succ n =>
        simp only [LogLaplacianEvenResidueVanishing.c, ↓reduceIte, RS16Center.center, coeff_mk, Nat.succ_ne_zero]; simp only [map_div₀, map_mul, map_sub, map_one, map_pow, map_ofNat, map_natCast]
        rfl
    have hlog : mk (LogLaplacianEvenResidueVanishing.c (Real.pi/2)) * (1+RS16Series.expScale (-1)) = 1 := by
      have hh := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) local_center_logistic
      have hexp : PowerSeries.map (algebraMap ℚ ℂ) (rescale (-1) (exp ℚ)) = RS16Series.expScale (-1) := by ext n; simp [coeff_map, coeff_rescale, local_RS16Series_coeff_expScale, div_eq_mul_inv]
      simpa only [map_mul, map_add, map_one, ← hc, hexp] using hh
    have hden : 1-C (2*(Real.cos (2*(Real.pi/2)) : ℂ))*RS16Series.expScale (-1)+RS16Series.expScale (-2) = (1+RS16Series.expScale (-1))^2 := by
      have he := exp_mul_exp_eq_exp_add (-1 : ℂ) (-1 : ℂ)
      change RS16Series.expScale (-1)*RS16Series.expScale (-1) = RS16Series.expScale (-1 + -1) at he; norm_num at he
      have hcos : Real.cos (2*(Real.pi/2)) = -1 := by rw [show 2*(Real.pi/2) = Real.pi by ring, Real.cos_pi]
      rw [hcos]; norm_num; rw [pow_two, ← he]; simp only [map_ofNat]; ring
    rw [hden, ← mul_pow, hlog, one_pow]
  have local_RS16Series_coeff_product (f g : PowerSeries ℂ) (n : ℕ) : coeff n (f*g) = ∑ q ∈ range (n+1), coeff q f * coeff (n-q) g := by rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have local_RS16_derivative_bridge (m : ℕ) (α : ℝ) (hs : ∀ n, Odd n → LogLaplacianEvenResidueVanishing.shifted α n = 0) : ∀ j ≤ m, LogLaplacianEvenResidueVanishing.derivativeArray α j = ∑ k ∈ range (m+1), if k ≤ j ∧ Odd k then (k+1 : ℂ)*LogLaplacianEvenResidueVanishing.shifted α (k+1)*((1/2 : ℂ)^(j-k)/((j-k) ! : ℂ)) else 0 := by
    have hcoeff (n : ℕ) : LogLaplacianEvenResidueVanishing.shifted α n = coeff n (RS16Series.expScale (-1/2) * PowerSeries.mk (LogLaplacianEvenResidueVanishing.A α)) := by
      rw [local_RS16Series_coeff_product]; simp only [local_RS16Series_coeff_expScale, PowerSeries.mk, coeff_mk]
      rfl
    have hss : ∀ n, Odd n → coeff n (RS16Series.expScale (-1/2) * PowerSeries.mk (LogLaplacianEvenResidueVanishing.A α)) = 0 := by intro n hn; rw [← hcoeff]; exact hs n hn
    intro j hj; rw [LogLaplacianEvenResidueVanishing.derivativeArray, local_derivative_coeff_reconstruction (LogLaplacianEvenResidueVanishing.A α) hss j]; simp_rw [← hcoeff]
    let f := fun k => if k ≤ j ∧ Odd k then (k+1 : ℂ)*LogLaplacianEvenResidueVanishing.shifted α (k+1)*((1/2 : ℂ)^(j-k)/((j-k) ! : ℂ)) else 0
    have hsmall : (∑ k ∈ range (j+1), if Odd k then (k+1 : ℂ)*LogLaplacianEvenResidueVanishing.shifted α (k+1)*((1/2 : ℂ)^(j-k)/((j-k) ! : ℂ)) else 0) = ∑ k ∈ range (j+1), f k := by
      apply sum_congr rfl; intro k hk
      have hkj : k ≤ j := Nat.le_of_lt_succ (mem_range.mp hk)
      simp [f, hkj]
    rw [hsmall]; apply sum_subset (range_mono (by omega)); intro k hk hkj
    have hnot : ¬k ≤ j := by simp only [mem_range] at hkj; omega
    simp [f, hnot]
  have local_RS16_result_of_structure : ∀ m : ℕ, Even m → ∀ α : ℝ, 0 < α → α < Real.pi → (∀ n, Odd n → shifted α n = 0) → annihilates m → (∀ j ≤ m, derivativeArray α j = ∑ k ∈ range (m + 1), if k ≤ j ∧ Odd k then (k + 1 : ℂ) * shifted α (k+1) * ((1/2 : ℂ)^(j-k) / ((j-k) ! : ℂ)) else 0) → paperBracket m α = 0 := by
    intro m hm α hα hπα hshift hann hbridge
    have hz := local_odd_convolution_zero m α hann hbridge
    have hpaper := local_RS16_paper_to_derivative m α
    rw [hpaper, hz, neg_zero]
  have local_RS16_shifted_even_of_square (α : ℝ) (hα : 0 < α) (hπα : α < Real.pi) (hsq : (mk (LogLaplacianEvenResidueVanishing.c α))^2 * (1 - C (2*(Real.cos (2*α) : ℂ))*RS16Series.expScale (-1) + RS16Series.expScale (-2)) = 1) : ∀ n, Odd n → LogLaplacianEvenResidueVanishing.shifted α n = 0 := by
    have hsin : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπα).ne'
    have hc : constantCoeff (mk (LogLaplacianEvenResidueVanishing.c α)) ≠ 0 := by simp only [constantCoeff_mk, LogLaplacianEvenResidueVanishing.c]; exact one_div_ne_zero (mul_ne_zero (by norm_num) hsin)
    have hcEven := local_RS16Series_centered_square_even (mk (LogLaplacianEvenResidueVanishing.c α)) (Real.cos (2*α) : ℂ) hc hsq
    have hAEven := local_shifted_A_odd (LogLaplacianEvenResidueVanishing.d α) (LogLaplacianEvenResidueVanishing.c α) LogLaplacianEvenResidueVanishing.w hcEven
    intro n hn
    have hh := hAEven n hn
    change coeff n (RS16Series.expScale (-1/2) * mk (LogLaplacianEvenResidueVanishing.A α)) = 0 at hh; rw [local_RS16Series_coeff_product] at hh; simpa only [local_RS16Series_coeff_expScale, coeff_mk, LogLaplacianEvenResidueVanishing.shifted] using hh
  have local_RS16_paper_zero_of_square_and_ann (m : ℕ) (hm : Even m) (α : ℝ) (hα : 0 < α) (hπα : α < Real.pi) (hsq : (mk (LogLaplacianEvenResidueVanishing.c α))^2 * (1 - C (2*(Real.cos (2*α) : ℂ))*RS16Series.expScale (-1) + RS16Series.expScale (-2)) = 1) (hann : LogLaplacianEvenResidueVanishing.annihilates m) : LogLaplacianEvenResidueVanishing.paperBracket m α = 0 := by
    have hs := local_RS16_shifted_even_of_square α hα hπα hsq
    exact local_RS16_result_of_structure m hm α hα hπα hs hann (local_RS16_derivative_bridge m α hs)
  have local_RS16_paper_zero_of_primary_square (m : ℕ) (hm : Even m) (α : ℝ) (hα : 0 < α) (hπα : α < Real.pi) (hsq : (mk (LogLaplacianEvenResidueVanishing.c α))^2 * (1-C (2*(Real.cos (2*α) : ℂ))*RS16Series.expScale (-1)+RS16Series.expScale (-2)) = 1) : LogLaplacianEvenResidueVanishing.paperBracket m α = 0 :=
    local_RS16_paper_zero_of_square_and_ann m hm α hα hπα hsq (LogLaplacianEvenResidueVanishing.bernoulli_annihilates m hm)
  intro m hm α hα hπα
  have hsq : (mk (c α))^2 * (1-C (2*(Real.cos (2*α) : ℂ))*RS16Series.expScale (-1)+RS16Series.expScale (-2)) = 1 := by
    by_cases hne : α = Real.pi/2
    · subst α
      exact local_RS16_center_primary_square
    · exact primary_square_inverse α hα hπα hne
  exact local_RS16_paper_zero_of_primary_square m hm α hα hπα hsq
end LogLaplacianEvenResidueVanishing
end D5.S3.ArithSums
