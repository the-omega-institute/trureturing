/- GID: D5/S3/Topology/WeavingCoefficientConsumer
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingCoefficientConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Uniform graph coefficient estimates on the actual ordered weaving reference graphs. -/

import D5.S3.Topology.WeavingStateGraphBridge
import D5.S3.Combinatorics.Graph.Polynomials.TutteCoefficientAsymptotics
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic

/-! Uniform graph coefficient estimates on the actual ordered weaving reference graphs. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Topology.WeavingCoefficientConsumer

open D5.S3.Topology.WeavingDiagramPorts
open D5.S3.Topology.WeavingMixedComponents
open D5.S3.Topology.WeavingReferenceIncidence
open D5.S3.Topology.WeavingReferenceDegree
open D5.S3.Topology.WeavingStateGraphBridge
open D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate
open D5.S3.Combinatorics.Graph.Polynomials.TutteCoefficientAsymptotics

theorem ordered_edge_card (P : Parameters) (p : ℕ) (hp : p < 2) :
    Nat.card (orderedGraph P p hp).edgeSet = P.n*P.m := by
  rw [← Nat.card_congr ((orderedGraphIso P p hp).mapEdgeSet)]
  exact referenceGraph_edge_card P p hp

def d (n : ℕ) : ℕ := n%2
def r (n : ℕ) : ℕ := (n-n%2)/2

theorem parity_decomposition (n : ℕ) : n = 2*r n+d n ∧ d n ≤ 1 := by
  unfold r d
  omega

/-- Nat subtraction is justified by the exact counts, not treated as integer
subtraction without a proof. Both resulting cycle ranks are positive. -/
theorem exact_cycle_ranks (P : Parameters) :
    (P.n*P.m+1-vertexCount P 1 = (r P.n+d P.n)*P.m-d P.n) ∧
    (P.n*P.m+1-vertexCount P 0 = r P.n*P.m+d P.n) := by
  have hv₁ := vertexCount_eq_circle_card P 1 (by omega)
  have hv₀ := vertexCount_eq_circle_card P 0 (by omega)
  rw [even_circle_count] at hv₁
  rw [odd_circle_count] at hv₀
  have hd := parity_decomposition P.n
  have hm := P.hm
  have hn := P.hn
  change vertexCount P 1 = r P.n*P.m+1+d P.n at hv₁
  change vertexCount P 0 = (r P.n+d P.n)*P.m+1-d P.n at hv₀
  have he : P.n*P.m = 2*(r P.n*P.m)+d P.n*P.m := by
    nth_rw 1 [hd.1]
    ring
  have hr : 1 ≤ r P.n := by unfold r; omega
  have hprod : 3 ≤ r P.n*P.m := by nlinarith
  constructor <;> rw [show (r P.n+d P.n)*P.m = r P.n*P.m+d P.n*P.m by ring] at * <;>
    omega

def H (P : Parameters) (p : ℕ) (hp : p < 2) : Polynomial ℤ :=
  mixedStatePolynomial P p hp

theorem actual_signed_estimate (P : Parameters) (p : ℕ) (hp : p < 2)
    (k : ℕ) (hk : 1 ≤ k) :
    ((H P p hp).coeff k - (-1 : ℤ)^k *
      ((P.n*P.m+1-vertexCount P p)+k-1).choose k).natAbs ≤
      uniformCoefficientConstant 4 k * (P.n*P.m+1)^(k-1) := by
  have h := signed_tutte_coefficient_estimate (vertexCount_pos P p hp)
    (orderedGraph P p hp) (orderedGraph_connected P p hp)
    (orderedGraph_forward_degree P p hp) k hk
  rw [ordered_edge_card] at h
  rw [graphStatePolynomial_eq_mixed] at h
  exact h

/-- Reverse triangle inequality removes the sign without assuming an eventual
coefficient sign. -/
theorem unsigned_error (a : ℤ) (B k R : ℕ)
    (h : (a-(-1 : ℤ)^k*(B : ℤ)).natAbs ≤ R) :
    ((a.natAbs : ℤ)-(B : ℤ)).natAbs ≤ R := by
  have hrev := abs_abs_sub_abs_le_abs_sub a ((-1 : ℤ)^k*(B : ℤ))
  have hbound : |a-(-1 : ℤ)^k*(B : ℤ)| ≤ (R : ℤ) := by
    have hc : (((a-(-1 : ℤ)^k*(B : ℤ)).natAbs : ℕ) : ℤ) ≤ (R : ℤ) := by
      exact_mod_cast h
    simpa only [Int.natCast_natAbs] using hc
  have hs : |(-1 : ℤ)^k*(B : ℤ)| = (B : ℤ) := by
    simp [abs_mul,abs_pow]
  have ha : |a| = (a.natAbs : ℤ) := by simp only [Int.natCast_natAbs]
  rw [hs,ha] at hrev
  have hc : |(a.natAbs : ℤ)-(B : ℤ)| ≤ (R : ℤ) := hrev.trans hbound
  have hc' : (((((a.natAbs : ℤ)-(B : ℤ)).natAbs : ℕ) : ℤ)) ≤ (R : ℤ) := by
    simpa only [Int.natCast_natAbs] using hc
  exact_mod_cast hc'

/-- One unsigned coefficient from each graph, with the exact two b-values.
This expression has no extra factor of two from a second copy of either tail. -/
theorem two_reference_unsigned_error (P : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    ((((H P 1 (by omega)).coeff k).natAbs +
        ((H P 0 (by omega)).coeff k).natAbs : ℤ) -
      (((((r P.n+d P.n)*P.m-d P.n)+k-1).choose k : ℕ) : ℤ) -
      ((((r P.n*P.m+d P.n)+k-1).choose k : ℕ) : ℤ)).natAbs ≤
      (2*uniformCoefficientConstant 4 k*(P.n*P.m+1)^(k-1) : ℕ) := by
  have h₁ := unsigned_error ((H P 1 (by omega)).coeff k)
    (((P.n*P.m+1-vertexCount P 1)+k-1).choose k) k
    (uniformCoefficientConstant 4 k*(P.n*P.m+1)^(k-1))
    (actual_signed_estimate P 1 (by omega) k hk)
  have h₀ := unsigned_error ((H P 0 (by omega)).coeff k)
    (((P.n*P.m+1-vertexCount P 0)+k-1).choose k) k
    (uniformCoefficientConstant 4 k*(P.n*P.m+1)^(k-1))
    (actual_signed_estimate P 0 (by omega) k hk)
  rw [(exact_cycle_ranks P).1] at h₁
  rw [(exact_cycle_ranks P).2] at h₀
  generalize ha : ((H P 1 (by omega)).coeff k).natAbs = A at *
  generalize hb : ((H P 0 (by omega)).coeff k).natAbs = B at *
  calc
    _ = (((A : ℤ) - (((((r P.n+d P.n)*P.m-d P.n)+k-1).choose k : ℕ) : ℤ)) +
      ((B : ℤ) - ((((r P.n*P.m+d P.n)+k-1).choose k : ℕ) : ℤ))).natAbs := by
      apply congrArg Int.natAbs
      push_cast
      ring
    _ ≤ _ := Int.natAbs_add_le _ _
    _ ≤ _ := Nat.add_le_add h₁ h₀
    _ = _ := by ring

/-- Explicit constants for the lower-degree error in a rising factorial. -/
def risingErrorConstant : ℕ → ℕ
  | 0 => 0
  | k+1 => (k+1)*risingErrorConstant k+k

theorem rising_factorial_bounds (b k : ℕ) :
    b^k ≤ b.ascFactorial k ∧
    b.ascFactorial k ≤ b^k+risingErrorConstant k*(b+1)^(k-1) := by
  induction k with
  | zero => simp [risingErrorConstant]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp [risingErrorConstant,Nat.ascFactorial_succ]
    have hpow : (b+1)*(b+1)^(k-1) = (b+1)^k := by
      conv_rhs => rw [show k = (k-1)+1 by omega]
      rw [pow_succ]
      ring
    constructor
    · rw [Nat.ascFactorial_succ,pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul (by omega : b ≤ b+k) ih.1
    · calc
        b.ascFactorial (k+1) = (b+k)*b.ascFactorial k := Nat.ascFactorial_succ
        _ ≤ (b+k)*(b^k+risingErrorConstant k*(b+1)^(k-1)) :=
          Nat.mul_le_mul_left _ ih.2
        _ = b^(k+1)+k*b^k+(b+k)*risingErrorConstant k*(b+1)^(k-1) := by
          rw [pow_succ]
          ring
        _ ≤ b^(k+1)+k*(b+1)^k+
            ((k+1)*(b+1))*risingErrorConstant k*(b+1)^(k-1) := by
          gcongr <;> nlinarith
        _ = b^(k+1)+risingErrorConstant (k+1)*(b+1)^k := by
          rw [show ((k+1)*(b+1))*risingErrorConstant k*(b+1)^(k-1) =
            (k+1)*risingErrorConstant k*((b+1)*(b+1)^(k-1)) by ring,hpow]
          simp only [risingErrorConstant,Nat.add_sub_cancel]
          ring

/-- A quantitative binomial leading term in b, proved from the exact factorial
identity. No fixed-graph asymptotic is assumed. -/
theorem binomial_leading_error (b k : ℕ) :
    |((b+k-1).choose k : ℝ)-(b : ℝ)^k/(k.factorial : ℝ)| ≤
      (risingErrorConstant k : ℝ)/(k.factorial : ℝ)*(b+1 : ℝ)^(k-1) := by
  have hlo := (rising_factorial_bounds b k).1
  have hhi := (rising_factorial_bounds b k).2
  rw [Nat.ascFactorial_eq_factorial_mul_choose'] at hlo hhi
  have hl : (b : ℝ)^k ≤ (k.factorial : ℝ)*((b+k-1).choose k : ℝ) := by
    exact_mod_cast hlo
  have hh : (k.factorial : ℝ)*((b+k-1).choose k : ℝ) ≤
      (b : ℝ)^k+(risingErrorConstant k : ℝ)*(b+1 : ℝ)^(k-1) := by
    exact_mod_cast hhi
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hn : 0 ≤ ((b+k-1).choose k : ℝ)-(b : ℝ)^k/(k.factorial : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hf).mpr (by nlinarith)
  rw [abs_of_nonneg hn]
  apply (mul_le_mul_iff_right₀ hf).mp
  calc
    _ = (k.factorial : ℝ)*((b+k-1).choose k : ℝ)-(b : ℝ)^k := by
      field_simp [ne_of_gt hf]
      <;> ring
    _ ≤ (risingErrorConstant k : ℝ)*(b+1 : ℝ)^(k-1) := by linarith
    _ = _ := by field_simp [ne_of_gt hf]

end D5.S3.Topology.WeavingCoefficientConsumer
