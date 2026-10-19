/- GID: D5/S3/Combinatorics/PowerSeries/HannaA271960DyadicVanishing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/HannaA271960DyadicVanishing
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Reversion and dyadic coefficient decimation prove Hanna's A271960 conjecture. -/

/-
result:
  proof_shape: content (dyadic support induction and stabilized series construction)
  escape_witness: none
  admission_basis: open-problem-resolution (#19138; Proved)
Direct frozen dependencies (declaration identities at the merged dev base):
  D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient
    statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
  D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.square_linear
    statement_id: sha256:c86b1a97015829f5473a85735d05b2d28ce1669bd9b20245fc14eba2df19edae
  D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.subst_two_agree
    statement_id: sha256:df6eb612af289b17ac13e3bc808e1777f8c9ae9eb942221828b083e4dd08f083
  D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.inverse_exists
    statement_id: sha256:2904de6f4cbe7c37a40fbf663d2e985f57c76b94fc4fb4c97cb67464c2dfaa12
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19172.
Coefficient agreement is written out; its original coefficient lemmas are reused directly.
Definitions have no independent proof claim and have escape_witness: none:
  IsGF: bind-only; consumers claim, inverse_squared, is_gf_of_squared_inverse.
  xOverA: bind-only; consumers claim, lagrange_bridge.
  claim: bind-only; consumer result.
  newton: bind-only; consumers newton_one, newton_agree, approximation_one, normalized.
  normalized: bind-only; consumers normalized_agree, normalized_one, normalized_equation,
    inverse_solution_exists.
Private theorem classifications (all have escape_witness: none):
  inverse_squared: bind-only; consumer result.
  lagrange_bridge: bind-only; consumer result.
  reflect_square_subst: bind-only; consumer odd_of_square.
  odd_of_square: bind-only; consumer result.
  odd_power_even_coeff: bind-only; consumer dyadic_vanishing.
  binomial_coeff: bind-only; consumer dyadic_vanishing.
  dyadic_vanishing: content (inductive support invariant); consumer result.
  newton_one: bind-only; consumer approximation_one.
  newton_agree: bind-only; consumers approximation_stable, normalized_equation.
  approximation_one: bind-only (iteration preserves constant coefficient one); consumers
    approximation_stable, normalized_equation.
  approximation_stable: content (coefficient stabilization induction); consumer normalized_agree.
  normalized_agree: content (stabilization at every degree); consumers normalized_one, normalized_equation.
  normalized_one: bind-only; consumers normalized_equation, inverse_solution_exists.
  normalized_equation: content (fixed point of the stabilized construction); consumer inverse_solution_exists.
  inverse_solution_exists: content (constructed inverse series); consumer generating_exists.
  is_gf_of_squared_inverse: bind-only; consumer generating_exists.
  generating_exists: content (constructed normalized generating function); consumer result.
-/

import D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo

set_option autoImplicit false

namespace D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing

open _root_.PowerSeries

/-- OEIS A271960: "G.f. A(x) satisfies: A(x)^2 = A( (x + 2*A(x)^2)^2 )", with A(x) = x + 2*x^2 + ... (offset 1). -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧
    A ^ 2 = PowerSeries.subst ((X + 2 * A ^ 2) ^ 2 : PowerSeries ℚ) A

/-- `x/A(x)`: the multiplicative inverse of the unit `A(x)/x`. -/
noncomputable def xOverA (A : PowerSeries ℚ) : PowerSeries ℚ :=
  (PowerSeries.mk fun n => coeff (n + 1) A)⁻¹

/-- OEIS A271960 (P. D. Hanna), conjecture: "[x^(2^n-2^k)] (x/A(x))^(2^n) = 0 for k = 0..n-2 and n >= 2." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n k : ℕ, 2 ≤ n → k ≤ n - 2 →
      coeff (2 ^ n - 2 ^ k) (xOverA A ^ (2 ^ n)) = 0

end D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing

namespace D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing
open _root_.PowerSeries
open D5.S1.Recurrence.Invariants.SignedCatalanCubicSubstitutionModThree

private theorem inverse_squared {A B : PowerSeries ℚ} (hA : IsGF A)
    (hB : constantCoeff B = 0) (hAB : A.subst B = X) (hBA : B.subst A = X) :
    B.subst (X ^ 2) = (B + 2 * X ^ 2) ^ 2 := by
  have hsA : HasSubst A := .of_constantCoeff_zero hA.1
  have hsB : HasSubst B := .of_constantCoeff_zero hB
  have hsI : HasSubst ((X + 2 * A ^ 2) ^ 2) := .of_constantCoeff_zero (by
    change constantCoeff ((X + 2 * A ^ 2) ^ 2) = 0
    simp [hA.1])
  have htwo (F : PowerSeries ℚ) : (2 : PowerSeries ℚ).subst F = 2 := by
    simpa only [map_ofNat] using (subst_C (a := F) (2 : ℚ))
  have he := congrArg (subst B) hA.2.2
  rw [subst_pow hsB, hAB, subst_comp_subst_apply hsI hsB,
    subst_pow hsB, subst_add hsB, subst_X hsB, subst_mul hsB, htwo,
    subst_pow hsB, hAB] at he
  have hsH : HasSubst ((B + 2 * X ^ 2) ^ 2) := .of_constantCoeff_zero (by
    change constantCoeff ((B + 2 * X ^ 2) ^ 2) = 0
    simp [hB])
  have he' := congrArg (fun F : PowerSeries ℚ => B.subst F) he
  have hc := congrArg (subst ((B+2*X^2)^2)) hBA
  rw [subst_comp_subst_apply hsA hsH B, subst_X hsH] at hc
  exact he'.trans hc

private theorem lagrange_bridge {A B : PowerSeries ℚ}
    (hA0 : constantCoeff A = 0) (hA1 : coeff 1 A = 1)
    (hB0 : constantCoeff B = 0) (hAB : A.subst B = X)
    (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) :
    coeff (N-r) (xOverA A ^ N) * r = N * coeff N (B ^ r) := by
  let U : PowerSeries ℚ := mk fun n => coeff (n+1) A
  have hU : constantCoeff U = 1 := by simpa [U, coeff_zero_eq_constantCoeff] using hA1
  have hAU : A = X * U := by
    simpa only [hA0, map_zero, add_zero] using eq_X_mul_shift_add_const A
  have hsB : HasSubst B := .of_constantCoeff_zero hB0
  have hX : xOverA A = U⁻¹ := rfl
  have hmul : U * U⁻¹ = 1 := PowerSeries.mul_inv_cancel U (by rw [hU]; norm_num)
  have hsub : B * U.subst B = X := by
    simpa [hAU, subst_mul hsB, subst_X hsB] using hAB
  have hfix : B = X * subst B (xOverA A) := by
    have hm := congrArg (subst B) hmul
    rw [subst_mul hsB] at hm
    have ho : (1 : PowerSeries ℚ).subst B = 1 := by simpa using (subst_C (a := B) (1 : ℚ))
    rw [ho] at hm
    rw [hX]
    calc
      B = B * (U.subst B * (U⁻¹).subst B) := by rw [hm, mul_one]
      _ = X * (U⁻¹).subst B := by rw [← mul_assoc, hsub]
  have h := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
    B (xOverA A) hB0 hfix N r hr hrN
  simpa only [mul_comm] using h.symm

private theorem reflect_square_subst (B : PowerSeries ℚ) :
    rescale (-1 : ℚ) (B.subst (X ^ 2)) = B.subst (X ^ 2) := by
  rw [rescale_eq_subst,
    subst_comp_subst_apply (.X_pow (two_ne_zero : (2 : ℕ) ≠ 0)) (.smul_X' (-1 : ℚ)),
    subst_pow (.smul_X' (-1 : ℚ)), subst_X (.smul_X' (-1 : ℚ))]
  simp

private theorem odd_of_square {B H : PowerSeries ℚ}
    (hH1 : coeff 1 H = 1) (hsq : H ^ 2 = B.subst (X ^ 2)) :
    rescale (-1 : ℚ) H = -H := by
  have he : (rescale (-1 : ℚ) H) ^ 2 = H ^ 2 := by
    rw [← map_pow, hsq, reflect_square_subst]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with hh | hh
  · have hc := congrArg (coeff 1) hh
    simp only [coeff_rescale, pow_one, hH1] at hc
    norm_num at hc
  · exact hh

private theorem odd_power_even_coeff {H : PowerSeries ℚ}
    (hodd : rescale (-1 : ℚ) H = -H) {n j : ℕ}
    (hn : 2 ∣ n) (hj : ¬ 2 ∣ j) : coeff n (H ^ j) = 0 := by
  have hjodd : Odd j := Nat.not_even_iff_odd.mp (mt Even.two_dvd hj)
  have he := congrArg (coeff n) (map_pow (rescale (-1 : ℚ)) H j)
  rw [hodd, hjodd.neg_pow] at he
  simp only [coeff_rescale, map_neg] at he
  have hnp : (-1 : ℚ) ^ n = 1 := (even_iff_two_dvd.mpr hn).neg_one_pow
  rw [hnp, one_mul] at he
  linarith

private theorem binomial_coeff {B H : PowerSeries ℚ} (hB : B = H - 2 * X ^ 2)
    (N r : ℕ) (hN : 2*r < N) :
    coeff N (B ^ r) = ∑ j ∈ Finset.range (r+1),
      (r.choose j : ℚ) * (-2 : ℚ) ^ (r-j) * coeff (N-2*(r-j)) (H ^ j) := by
  classical
  rw [hB, sub_eq_add_neg, add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := Finset.mem_range_succ_iff.mp hj
  have hpower : (-(2 * X ^ 2) : PowerSeries ℚ) ^ (r-j) =
      C ((-2 : ℚ) ^ (r-j)) * X ^ (2*(r-j)) := by
    rw [show (-(2 * X ^ 2) : PowerSeries ℚ) = C (-2 : ℚ) * X ^ 2 by rw [map_neg, map_ofNat]; ring,
      mul_pow, map_pow, ← pow_mul]
  rw [hpower]
  have hrearrange : H ^ j * (C ((-2 : ℚ) ^ (r-j)) * X ^ (2*(r-j))) *
      (r.choose j : PowerSeries ℚ) =
      C ((r.choose j : ℚ) * (-2 : ℚ) ^ (r-j)) * (H ^ j * X ^ (2*(r-j))) := by
    simp only [map_mul, map_natCast]
    ring
  rw [hrearrange, coeff_C_mul, coeff_mul_X_pow', if_pos (by omega)]

private theorem dyadic_vanishing {B H : PowerSeries ℚ}
    (hB : B = H - 2 * X ^ 2) (hsq : H ^ 2 = B.subst (X ^ 2))
    (hodd : rescale (-1 : ℚ) H = -H) :
    ∀ s N r : ℕ, 2*r < N → 2^s ∣ N-2*r → r < 2^s → coeff N (B ^ r) = 0 := by
  intro s
  induction s with
  | zero =>
    intro N r hN hdiv hr
    have hr0 : r = 0 := Nat.lt_one_iff.mp hr
    subst r
    simp [coeff_one, show N ≠ 0 by omega]
  | succ s ih =>
    intro N r hN hdiv hr
    have hpow : 2^(s+1) = 2*2^s := Nat.pow_succ'
    have hD : 2 ∣ N - 2*r := (dvd_mul_right 2 (2^s)).trans (hpow ▸ hdiv)
    have hEven : 2 ∣ N := by omega
    rw [binomial_coeff hB N r hN]
    apply Finset.sum_eq_zero
    intro j hj
    have hjr : j ≤ r := Finset.mem_range_succ_iff.mp hj
    have hE : 2 ∣ N-2*(r-j) := by omega
    by_cases hj2 : 2 ∣ j
    · have hp : H ^ j = (B ^ (j/2)).subst (X ^ 2) := by
        calc
          H^j = (H^2)^(j/2) := by rw [← pow_mul, Nat.mul_div_cancel' hj2]
          _ = _ := by rw [hsq, subst_pow (.X_pow (two_ne_zero : (2 : ℕ) ≠ 0))]
      rw [hp, coeff_subst_X_pow (two_ne_zero : (2 : ℕ) ≠ 0), if_pos hE]
      have hindex : (N-2*(r-j))/2 = N/2-(r-j) := Nat.sub_mul_div N 2 (r-j)
      rw [hindex]
      have hbound : 2*(j/2) < N/2-(r-j) := by omega
      have hdifference : N/2-(r-j)-2*(j/2) = (N-2*r)/2 := by omega
      have hd : 2^s ∣ N/2-(r-j)-2*(j/2) := by
        rw [hdifference]
        obtain ⟨q, hq⟩ := hdiv
        rw [hq, hpow]
        refine ⟨q, ?_⟩
        simp [mul_assoc]
      have hr' : j/2 < 2^s := by rw [hpow] at hr; omega
      simp only [Algebra.algebraMap_self, RingHom.id_apply, ih _ _ hbound hd hr', mul_zero]
    · rw [odd_power_even_coeff hodd hE hj2, mul_zero]

private noncomputable def newton (F : PowerSeries ℚ) : PowerSeries ℚ :=
  F + C (1/2 : ℚ) * (F.subst (X ^ 2) - F ^ 2 - 2 * X)

private theorem newton_one {F : PowerSeries ℚ} (hF : constantCoeff F = 1) :
    constantCoeff (newton F) = 1 := by
  simp [newton, hF]

private theorem newton_agree {d : ℕ} (hd : 1 ≤ d) {F G : PowerSeries ℚ}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1)
    (h : ∀ n < d, coeff n F = coeff n G) :
    ∀ n < d+1, coeff n (newton F) = coeff n (newton G) := by
  intro n hn
  have hs := subst_two_agree hd h n hn
  have hl := square_linear hF hG h n hn
  simp only [newton, map_add, map_sub, coeff_C_mul]
  linarith

private theorem approximation_one (n : ℕ) : constantCoeff (((newton^[n]) 1)) = 1 := by
  have hmap : Set.MapsTo newton {F | constantCoeff F = 1} {F | constantCoeff F = 1} :=
    fun _ h => newton_one h
  exact hmap.iterate n constantCoeff_one

private theorem approximation_stable {d e : ℕ} (h : d ≤ e) :
    ∀ n < d+1, coeff n (((newton^[d]) 1)) = coeff n (((newton^[e]) 1)) := by
  induction d generalizing e with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    subst n
    simpa only [coeff_zero_eq_constantCoeff] using
      (approximation_one 0).trans (approximation_one e).symm
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      simpa only [Function.iterate_succ_apply'] using
        newton_agree (by omega : 1 ≤ d+1) (approximation_one d)
          (approximation_one e) (ih (by omega))

private noncomputable def normalized : PowerSeries ℚ :=
  mk fun n => coeff n (((newton^[n]) 1))

private theorem normalized_agree (d : ℕ) :
    ∀ n < d+1, coeff n normalized = coeff n (((newton^[d]) 1)) := by
  intro n hn
  simp only [normalized, coeff_mk]
  exact approximation_stable (by omega : n ≤ d) n (by omega)

private theorem normalized_one : constantCoeff normalized = 1 := by
  have h := normalized_agree 0 0 (by omega)
  simpa only [Function.iterate_zero_apply, coeff_zero_eq_constantCoeff, map_one] using h

private theorem normalized_equation : normalized.subst (X ^ 2) = normalized ^ 2 + 2 * X := by
  have hf : normalized = newton normalized := by
    ext n
    have hg := normalized_agree (n+1) n (by omega)
    have hs := newton_agree (by omega : 1 ≤ n+1) normalized_one (approximation_one n)
      (normalized_agree n) n (by omega)
    rw [Function.iterate_succ_apply'] at hg
    exact hg.trans hs.symm
  ext n
  have hc := congrArg (coeff n) hf
  simp only [newton, map_add, map_sub, coeff_C_mul] at hc ⊢
  linarith

private theorem inverse_solution_exists : ∃ B : PowerSeries ℚ,
    constantCoeff B = 0 ∧ coeff 1 B = 1 ∧
      B.subst (X ^ 2) = (B + 2 * X ^ 2) ^ 2 := by
  let H : PowerSeries ℚ := X * normalized.subst (X ^ 2)
  let B : PowerSeries ℚ := H - 2 * X ^ 2
  have hs : HasSubst ((X : PowerSeries ℚ) ^ 2) := .X_pow (two_ne_zero : (2 : ℕ) ≠ 0)
  have htwo : (2 : PowerSeries ℚ).subst ((X : PowerSeries ℚ) ^ 2) = 2 := by
    simpa only [map_ofNat] using (subst_C (a := (X : PowerSeries ℚ)^2) (2 : ℚ))
  refine ⟨B, by simp [B,H], ?_, ?_⟩
  · simp [B, H, coeff_subst_X_pow, coeff_zero_eq_constantCoeff, normalized_one]
  · have he := congrArg (subst ((X : PowerSeries ℚ)^2)) normalized_equation
    rw [subst_add hs, subst_pow hs, subst_mul hs, htwo, subst_X hs] at he
    have hB : B + 2*X^2 = H := sub_add_cancel H (2*X^2)
    rw [hB]
    dsimp only [B,H]
    rw [subst_sub hs, subst_mul hs, subst_X hs, subst_mul hs, htwo,
      subst_pow hs, subst_X hs, he]
    ring

private theorem is_gf_of_squared_inverse {A B : PowerSeries ℚ}
    (hA0 : constantCoeff A = 0) (hA1 : coeff 1 A = 1)
    (hB0 : constantCoeff B = 0) (hBA : B.subst A = X) (hAB : A.subst B = X)
    (hBsq : B.subst (X^2) = (B+2*X^2)^2) : IsGF A := by
  refine ⟨hA0,hA1,?_⟩
  have hsA : HasSubst A := .of_constantCoeff_zero hA0
  have hsB : HasSubst B := .of_constantCoeff_zero hB0
  have hs2 : HasSubst (A ^ 2) := .of_constantCoeff_zero' (by simp [hA0])
  have htwo : (2 : PowerSeries ℚ).subst A = 2 := by
    simpa only [map_ofNat] using (subst_C (a := A) (2 : ℚ))
  have he := congrArg (subst A) hBsq
  rw [subst_comp_subst_apply (.X_pow (two_ne_zero : (2 : ℕ) ≠ 0) : HasSubst ((X : PowerSeries ℚ)^2)) hsA,
    subst_pow hsA, subst_X hsA, subst_pow hsA, subst_add hsA,
    hBA, subst_mul hsA, htwo, subst_pow hsA, subst_X hsA] at he
  have hcancel (F : PowerSeries ℚ) (hF : HasSubst F) :
      PowerSeries.subst (PowerSeries.subst F B) A = F := by
    have hassoc := subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := ℚ)
      (a := B) (b := F) hsB hF A
    have h1 := congrArg (PowerSeries.subst (R := ℚ) F) hAB
    have h2 : PowerSeries.subst F (X : PowerSeries ℚ) = F := subst_X (R := ℚ) hF
    with_reducible exact hassoc.symm.trans (h1.trans h2)
  with_reducible exact (hcancel (A^2) hs2).symm.trans (congrArg (fun F : PowerSeries ℚ => PowerSeries.subst F A) he)


private theorem generating_exists : ∃ A, IsGF A := by
  obtain ⟨B, hB0, hB1, hBsq⟩ := inverse_solution_exists
  obtain ⟨A, hA0, hA1, hBA, hAB⟩ := inverse_exists B hB0 hB1
  exact ⟨A, is_gf_of_squared_inverse hA0 hA1 hB0 hBA hAB hBsq⟩

theorem result : D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing.claim := by
  refine ⟨generating_exists, ?_⟩
  intro A hA n k hn hk
  obtain ⟨B, hB0, hB1, hAB, hBA⟩ := inverse_exists A hA.1 hA.2.1
  let H : PowerSeries ℚ := B + 2*X^2
  have hHB : B = H-2*X^2 := (add_sub_cancel_right B (2*X^2)).symm
  have hHs : H^2 = B.subst (X^2) := (inverse_squared hA hB0 hAB hBA).symm
  have hH1 : coeff 1 H = 1 := by simp [H,hB1]
  have hHo : rescale (-1 : ℚ) H = -H := odd_of_square hH1 hHs
  have hkn : k+1 < n := by omega
  have hNR : 2*(2^k) < 2^n := by
    rw [← Nat.pow_succ']
    exact pow_lt_pow_right₀ (by decide) hkn
  have hdiv : 2^(k+1) ∣ 2^n - 2*(2^k) := by
    apply Nat.dvd_sub
    · exact pow_dvd_pow 2 (by omega : k+1 ≤ n)
    · rw [← Nat.pow_succ']
  have hr : 2^k < 2^(k+1) := pow_lt_pow_right₀ (by decide) (by omega)
  have hv := dyadic_vanishing hHB hHs hHo (k+1) (2^n) (2^k) hNR hdiv hr
  have hlag := lagrange_bridge hA.1 hA.2.1 hB0 hAB (2^n) (2^k)
    (Nat.one_le_pow k 2 (by decide)) (by omega)
  rw [hv, mul_zero] at hlag
  exact (mul_eq_zero.mp hlag).resolve_right (by positivity)


end D5.S3.Combinatorics.PowerSeries.HannaA271960DyadicVanishing
