import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced switchingVector flip_adj)
local notation "flip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private matrix_flip_prefix from D5.S3.Combinatorics.Graph.HypercubeCritical.GrayGridComponent
open private theta theta_flip theta_unit prod_true_sign from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GridWedgeSigning
open private matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-- The TRUE-prefix sign on the edge that flips coordinate `i`. -/
def truePrefixSign {n : ℕ} (x : Q n) (i : Fin n) : ℤ :=
  (-1) ^ ((univ : Finset (Fin n)).filter (fun j => j < i ∧ x j = true)).card

private lemma matrix_true_prefix {n : ℕ} (x : Q n) (i : Fin n) :
    huangMatrix n x (flip x i) =
      theta x * theta (flip x i) * (truePrefixSign x i : ℝ) := by
  classical
  rw [matrix_flip_prefix, theta_flip]
  have hfactor (j : Fin n) :
      (if j < i ∧ x j = false then (-1 : ℝ) else 1) =
        (if j < i then (-1 : ℝ) else 1) *
          (if j < i ∧ x j = true then (-1 : ℝ) else 1) := by
    by_cases hj : j < i <;> cases x j <;> simp [hj]
  simp_rw [hfactor]
  rw [prod_mul_distrib, prod_true_sign, prod_true_sign]
  have hcount : ((univ : Finset (Fin n)).filter (· < i)).card = i.val := by
    rw [show univ.filter (· < i) = Iio i by ext j; simp, Fin.card_Iio]
  rw [hcount]
  push_cast [truePrefixSign]
  rfl

/-- A balanced cubic support has integral TRUE-prefix switching signs and
obeys the signed neighbor equation at every vertex of the nine-cube. -/
theorem q9_integral_true_prefix_switching {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ z : Q 9 → ℤ,
      (∀ x ∈ C, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ C, z x = 0) ∧
      (∀ x ∈ C, ∀ i : Fin 9, flip x i ∈ C →
        truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ x, (∑ i : Fin 9, truePrefixSign x i * z (flip x i)) = 3 * z x := by
  classical
  obtain ⟨sigma, hs⟩ := hb
  let z : Q 9 → ℤ := fun x =>
    if x ∈ C then (if theta x * sigma x = 1 then 1 else -1) else 0
  have hunit (x : Q 9) (hx : x ∈ C) : theta x * sigma x = 1 ∨ theta x * sigma x = -1 := by
    rcases theta_unit x with h | h <;> rcases hs.1 x hx with h' | h' <;> simp [h, h']
  have hz (x : Q 9) : (z x : ℝ) = theta x * switchingVector C sigma x := by
    by_cases hx : x ∈ C
    · rcases hunit x hx with h | h <;> norm_num [z, switchingVector, hx, h]
    · simp [z, switchingVector, hx]
  refine ⟨z, ?_, fun x hx => by simp [z, hx], ?_, ?_⟩
  · intro x hx
    simp only [z, ite_eq_left hx]
    split <;> simp
  · intro x hx i hy
    have he := matrix_true_prefix x i
    rw [hs.2 x hx _ hy (flip_adj x i)] at he
    have hh : (truePrefixSign x i : ℝ) = (z x : ℝ) * (z (flip x i) : ℝ) := by
      rw [hz, hz, switchingVector, switchingVector, ite_eq_left hx, ite_eq_left hy]
      rcases theta_unit x with h | h <;> rcases theta_unit (flip x i) with h' | h' <;>
        rw [h, h'] at he ⊢ <;> linarith
    exact_mod_cast hh
  · intro x
    have h := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hreg hs) x
    change (huangMatrix 9).mulVec (switchingVector C sigma) x =
      3 * switchingVector C sigma x at h
    rw [matrix_row] at h
    change (∑ i : Fin 9, huangMatrix 9 x (flip x i) *
      switchingVector C sigma (flip x i)) = 3 * switchingVector C sigma x at h
    have hterm (i : Fin 9) : (truePrefixSign x i : ℝ) * (z (flip x i) : ℝ) =
        theta x * (huangMatrix 9 x (flip x i) * switchingVector C sigma (flip x i)) := by
      rw [hz]
      rw [matrix_true_prefix]
      rcases theta_unit x with ht | ht <;> simp [ht] <;> ring
    have heq : (∑ i : Fin 9, (truePrefixSign x i : ℝ) * (z (flip x i) : ℝ)) = 3 * (z x : ℝ) := by
      simp_rw [hterm]
      rw [← mul_sum, h, hz]
      ring
    exact_mod_cast heq

#print axioms q9_integral_true_prefix_switching

end D5.S3.Combinatorics.Graph.HypercubeCritical
