/- GID: D5/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/MatharA186335FiveTermRecurrence
   mirror-E: none(waiver:formal-power-series-proof)
   anchors: []
   utility: none
   digest: The source double sum A186335 satisfies Mathar's five-term recurrence. -/

/-
The source is OEIS A186335, FORMULA, interpreted on nonnegative legal pairs.
The integer-valued sequence is defined by the finite source sum, independently
of the recurrence. Natural subtraction is used only with the explicit support
conditions. The result includes every natural n ≥ 4 and has no extra hypothesis.

admission_basis: open-problem-resolution (#30472)
proof_shape: bind-only; escape_witness: none.
All private helpers are consumed by the source-identification, differential,
and coefficient-extraction path to result; none is a separate mathematical claim.
The direct frozen coefficient supplier is
D5/S1/Recurrence/A308815DFiniteRecurrence.euler_coeff.
The retained proof uses Mathlib's binomial, central-binomial and power-series
identities. Library/RecurrenceAlgebraic/mathar2015a186335.md gives the source
attestation and the limits of the external-standing evidence.
-/

import D5.S1.Recurrence.A308815DFiniteRecurrence
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

open Finset PowerSeries
namespace D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence

/-- The literal finite sum; support is checked before any natural subtraction is used. -/
def legal (n k j : ℕ) : Prop := j ≤ k ∧ k + j ≤ n ∧ n - k - j ≤ k - j
instance (n k j : ℕ) : Decidable (legal n k j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def sourcePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n+1)).product (range (n+1))).filter (fun p => legal n p.1 p.2)
def a (n : ℕ) : ℤ :=
  ∑ p ∈ sourcePairs n,
    ((p.1-p.2).choose (n-p.1-p.2) : ℤ) * (p.1.choose p.2 : ℤ) *
      ((2*(n-p.1-p.2)).choose (n-p.1-p.2) : ℤ)
def claim : Prop := ∀ n : ℕ, 4 ≤ n →
  (n:ℤ)*a n + (1-2*(n:ℤ))*a (n-1) + 5*(1-(n:ℤ))*a (n-2) +
    3*(2*(n:ℤ)-3)*a (n-3) + 5*((n:ℤ)-2)*a (n-4) = 0

/-- The two binomial factors really are the multinomial weights in the advisory route. -/
private theorem binomial_reindex (m j l : ℕ) :
    (m+l).choose m * (m+j+l).choose j =
      (m+j+l).choose m * (j+l).choose j := by
  have h := Nat.choose_mul (n := m+j+l) (k := m+l) (s := m) (by omega)
  rw [show m+j+l-m = j+l by omega, show m+l-m=l by omega] at h
  rw [Nat.choose_symm_of_eq_add (show m+j+l = (m+l)+j by omega),
    Nat.choose_symm_of_eq_add (show j+l = l+j by omega)] at h
  simpa only [mul_comm] using h

private def reindexedPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n+1)).product (range (n+1))).filter (fun p => 2*p.1+2*p.2 ≤ n)

private theorem source_sum_reindex (n : ℕ) : a n =
    ∑ p ∈ reindexedPairs n,
      ((n-p.1-2*p.2).choose p.1 : ℤ) * ((n-p.1-p.2).choose p.2 : ℤ) *
        ((2*p.1).choose p.1 : ℤ) := by
  unfold a
  apply Finset.sum_bij (s := sourcePairs n) (t := reindexedPairs n) (fun p _ => (n-p.1-p.2, p.2))
  · intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hj,hkj,hm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩ <;> dsimp <;> omega
  · intro p hp q hq heq
    rcases (Finset.mem_filter.mp hp).2 with ⟨hp1,hp2,hp3⟩
    rcases (Finset.mem_filter.mp hq).2 with ⟨hq1,hq2,hq3⟩
    have h1 : n-p.1-p.2 = n-q.1-q.2 := congrArg Prod.fst heq
    have h2 := congrArg (fun r : ℕ × ℕ => r.2) heq
    change p.2=q.2 at h2
    apply Prod.ext <;> omega
  · intro q hq
    have hq' : 2*q.1+2*q.2 ≤ n := (Finset.mem_filter.mp hq).2
    refine ⟨(n-q.1-q.2,q.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
      · dsimp; omega
      · dsimp; omega
      · change legal n (n-q.1-q.2) q.2
        unfold legal
        omega
    · apply Prod.ext <;> dsimp <;> omega
  · intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hj,hkj,hm⟩
    dsimp
    rw [show n-(n-p.1-p.2)-2*p.2 = p.1-p.2 by omega,
      show n-(n-p.1-p.2)-p.2 = p.1 by omega]

/-- The independently defined rational source series, with no recurrence assumption. -/
private noncomputable def sourceSeries : PowerSeries ℚ := mk (fun n => (a n : ℚ))
private noncomputable def P : PowerSeries ℚ := 1-2*X-5*X^2+6*X^3+5*X^4
private noncomputable def Q : PowerSeries ℚ := -1-5*X+9*X^2+10*X^3

/-- Exact five-term coefficient extraction, for all legal indices. -/
private theorem recurrence_of_ode (A : PowerSeries ℚ)
    (h : P*derivative A+Q*A=0) (n : ℕ) (hn : 4 ≤ n) :
    (n:ℚ)*coeff n A + (1-2*(n:ℚ))*coeff (n-1) A +
      5*(1-(n:ℚ))*coeff (n-2) A + 3*(2*(n:ℚ)-3)*coeff (n-3) A +
      5*((n:ℚ)-2)*coeff (n-4) A = 0 := by
  have hh := congrArg (fun f : PowerSeries ℚ => coeff n (X*f)) h
  have hex : X*(P*derivative A+Q*A) =
      X*derivative A - 2*(X^1*(X*derivative A)) - 5*(X^2*(X*derivative A)) +
      6*(X^3*(X*derivative A)) + 5*(X^4*(X*derivative A)) -
      X^1*A - 5*(X^2*A) + 9*(X^3*A) + 10*(X^4*A) := by
    dsimp [P,Q]
    ring
  rw [hex] at hh
  simp only [map_add, map_sub, coeff_ofNat_mul,
    mul_zero, map_zero] at hh
  simp only [coeff_X_pow_mul', ite_eq_left (by omega : 1 ≤ n),
    ite_eq_left (by omega : 2 ≤ n), ite_eq_left (by omega : 3 ≤ n), ite_eq_left hn,
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff] at hh
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub hn] at hh
  linear_combination hh


private noncomputable def central : PowerSeries ℚ := mk (fun n => (n.centralBinom : ℚ))
private noncomputable def D : PowerSeries ℚ := 1-X-X^2
private noncomputable def B : PowerSeries ℚ := D⁻¹
private noncomputable def z : PowerSeries ℚ := X^2*B
private noncomputable def generated : PowerSeries ℚ := B * central.subst z

private lemma coeff_subst_range (f g : PowerSeries ℚ) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (f.subst g) = ∑ k ∈ range (n+1), coeff k f * coeff n (g^k) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply mem_range.mpr
  by_contra hn
  have hz : coeff n (g^k) = 0 := by
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast (by omega : n < k))
      (le_order_pow_of_constantCoeff_eq_zero k hg)
  exact hk (by simp [hz])

private lemma central_ode : (1-4*X)*derivative central - 2*central = 0 := by
  ext n
  have hh : ((n+1 : ℕ) : ℚ) * ((n+1).centralBinom : ℚ) =
      2*(2*(n:ℚ)+1)*(n.centralBinom : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  simp only [sub_mul, one_mul, mul_assoc, map_sub, coeff_ofNat_mul,
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff,
    coeff_derivative, central, coeff_mk, map_zero]
  push_cast at hh ⊢
  linear_combination hh

private lemma B_mul_D : B*D = 1 := by
  exact PowerSeries.inv_mul_cancel D (by simp [D])

private lemma z_constant : constantCoeff z = 0 := by simp [z]

private lemma kernel_identity (m : ℕ) :
    ((mk (fun n => ((m+n).choose m : ℚ))).subst (X+X^2)) = B^(m+1) := by
  have hg : HasSubst (X+X^2 : PowerSeries ℚ) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hh := congrArg (fun f : PowerSeries ℚ => (substAlgHom hg) f)
    (mk_add_choose_mul_one_sub_pow_eq_one ℚ m)
  simp only [map_mul, map_pow, map_sub, map_one, substAlgHom_X] at hh
  rw [coe_substAlgHom] at hh
  have he : (1-(X+X^2) : PowerSeries ℚ) = D := by dsimp [D]; ring
  rw [he] at hh
  have hb : B^(m+1)*D^(m+1) = 1 := by rw [← mul_pow, B_mul_D, one_pow]
  exact mul_right_cancel₀ (pow_ne_zero _ (by intro h; have := congrArg constantCoeff h; simp [D] at this))
    (hh.trans hb.symm)


private lemma binomial_power_coeff (r d : ℕ) :
    coeff d ((X+X^2 : PowerSeries ℚ)^r) =
      if r ≤ d then (r.choose (d-r) : ℚ) else 0 := by
  have he : (X+X^2 : PowerSeries ℚ)^r = X^r*(1+X)^r := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he, coeff_X_pow_mul']
  split_ifs with h
  · have hh : (1+X : PowerSeries ℚ)^r =
        (((1+Polynomial.X : Polynomial ℚ)^r) : PowerSeries ℚ) := by simp
    rw [hh, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  · rfl

private lemma kernel_coeff (m d : ℕ) : coeff d (B^(m+1)) =
    ∑ j ∈ range (d+1), ((m+d-j).choose m : ℚ) * ((d-j).choose j : ℚ) := by
  rw [← kernel_identity, coeff_subst_range _ _ (by simp)]
  simp only [coeff_mk]
  rw [← sum_range_reflect (fun r => ((m+r).choose m : ℚ) *
    coeff d ((X+X^2 : PowerSeries ℚ)^r)) (d+1)]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d := by simp only [mem_range] at hj; omega
  simp only [Nat.add_sub_cancel]
  rw [binomial_power_coeff, if_pos (by omega), show d-(d-j)=j by omega,
    show m+(d-j)=m+d-j by omega]


private lemma source_kernel (n : ℕ) : (a n : ℚ) =
    ∑ m ∈ range (n+1), (m.centralBinom : ℚ) * coeff n (X^(2*m)*B^(m+1)) := by
  rw [source_sum_reindex]
  push_cast
  unfold reindexedPairs
  rw [Finset.sum_filter]
  trans ∑ m ∈ range (n+1), ∑ j ∈ range (n+1),
    if 2*m+2*j ≤ n then
      ((n-m-2*j).choose m : ℚ)*((n-m-j).choose j : ℚ)*((2*m).choose m : ℚ)
    else 0
  · exact Finset.sum_product (range (n+1)) (range (n+1)) _
  apply sum_congr rfl
  intro m hm
  rw [coeff_X_pow_mul']
  by_cases hmn : 2*m ≤ n
  · rw [if_pos hmn, kernel_coeff]
    have hext : (∑ j ∈ range (n-2*m+1),
        ((m+(n-2*m)-j).choose m : ℚ)*((n-2*m-j).choose j : ℚ)) =
        ∑ j ∈ range (n+1),
        ((m+(n-2*m)-j).choose m : ℚ)*((n-2*m-j).choose j : ℚ) := by
      apply sum_subset
      · intro j hj
        simp only [mem_range] at hj ⊢
        omega
      · intro j hj hnot
        have hz : (n-2*m-j).choose j = 0 := Nat.choose_eq_zero_of_lt (by
          simp only [mem_range] at hj hnot
          omega)
        simp [hz]
    rw [hext, mul_sum]
    apply sum_congr rfl
    intro j hj
    by_cases h : 2*m+2*j ≤ n
    · rw [if_pos h]
      have hb := binomial_reindex m j (n-2*m-2*j)
      rw [show m+(n-2*m-2*j)=n-m-2*j by omega,
        show m+j+(n-2*m-2*j)=n-m-j by omega,
        show j+(n-2*m-2*j)=n-2*m-j by omega] at hb
      rw [show m+(n-2*m)-j=n-m-j by omega]
      have hbq : ((n-m-2*j).choose m : ℚ)*((n-m-j).choose j : ℚ) =
          ((n-m-j).choose m : ℚ)*((n-2*m-j).choose j : ℚ) := by exact_mod_cast hb
      simp only [Nat.centralBinom]
      linear_combination ((2*m).choose m : ℚ)*hbq
    · rw [if_neg h]
      have hz : (n-2*m-j).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hz]
  · rw [if_neg hmn, mul_zero]
    apply sum_eq_zero
    intro j hj
    rw [if_neg (by omega)]


private lemma generated_coeff (n : ℕ) : coeff n generated =
    ∑ m ∈ range (n+1), (m.centralBinom : ℚ) * coeff n (X^(2*m)*B^(m+1)) := by
  have he : coeff n (B*central.subst z) =
      coeff n (B * ∑ m ∈ range (n+1), C (m.centralBinom : ℚ)*z^m) := by
    rw [coeff_mul, coeff_mul]
    apply sum_congr rfl
    intro p hp
    have hp2 : p.2 ≤ n := by have := mem_antidiagonal.mp hp; omega
    congr 1
    rw [coeff_subst_range _ _ z_constant, map_sum]
    simp only [central, coeff_mk, coeff_C_mul]
    apply sum_subset
    · intro m hm
      simp only [mem_range] at hm ⊢
      omega
    · intro m hm hnot
      have hz : coeff p.2 (z^m) = 0 := by
        apply coeff_of_lt_order
        exact lt_of_lt_of_le (by exact_mod_cast (by simp only [mem_range] at hnot; omega : p.2 < m))
          (le_order_pow_of_constantCoeff_eq_zero m z_constant)
      simp [hz]
  rw [generated, he, mul_sum, map_sum]
  apply sum_congr rfl
  intro m hm
  have heq : B*(C (m.centralBinom : ℚ)*z^m) =
      C (m.centralBinom : ℚ)*(X^(2*m)*B^(m+1)) := by
    dsimp [z]
    rw [mul_pow, ← pow_mul, pow_succ]
    ring
  rw [heq, coeff_C_mul]

private lemma source_identification : sourceSeries = generated := by
  ext n
  rw [sourceSeries, coeff_mk, source_kernel, generated_coeff]

private lemma B_derivative : derivative B = (1+2*X)*B^2 := by
  simp only [B, derivative_inv', D, map_sub, derivative_one,
    derivative_X, derivative_pow, smul_eq_mul]
  ring

private lemma z_derivative : derivative z = X*(2-X)*B^2 := by
  have hb := B_mul_D
  dsimp [D] at hb
  dsimp [z]
  rw [Derivation.leibniz, derivative_pow, derivative_X, B_derivative]
  simp only [smul_eq_mul, mul_one]
  linear_combination -2*X*B*hb

private lemma P_B_square : P*B^2 = 1-4*z := by
  have hb := B_mul_D
  dsimp [P, D, z] at *
  linear_combination ((1-X-X^2)*B+1-4*X^2*B)*hb

private lemma generated_ode : P*derivative generated+Q*generated = 0 := by
  have hg : HasSubst z := HasSubst.of_constantCoeff_zero' z_constant
  have hs := congrArg (fun f : PowerSeries ℚ => (substAlgHom hg) f) central_ode
  simp only [map_sub, map_mul, map_one, map_ofNat, map_zero, substAlgHom_X] at hs
  rw [coe_substAlgHom] at hs
  have hp := P_B_square
  have hb := B_mul_D
  dsimp [generated]
  rw [Derivation.leibniz, derivative_subst hg, B_derivative, z_derivative]
  dsimp [P, Q, D, z] at *
  linear_combination
    ((1+2*X)*central.subst (X^2*B)+X*(2-X)*B*(derivative central).subst (X^2*B))*hp +
    X*(2-X)*B*hs - (1+2*X)*central.subst (X^2*B)*hb

theorem result : claim := by
  intro n hn
  have hs : P*derivative sourceSeries+Q*sourceSeries=0 := by
    rw [source_identification]
    exact generated_ode
  have h := recurrence_of_ode sourceSeries hs n hn
  simp only [sourceSeries, coeff_mk] at h
  exact_mod_cast h



end D5.S1.Recurrence.Algebraic.MatharA186335FiveTermRecurrence
