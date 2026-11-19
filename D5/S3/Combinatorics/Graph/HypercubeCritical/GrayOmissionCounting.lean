import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayPairCutCounting
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Nonnegative combinations of local omission inequalities. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.GrayOmissionCounting

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

inductive Row (V : Type*) where
  | degree (center : V)
  | star (center : V) (leaves : Finset V)

def demand (R : Finset V) : Row V → ℕ
  | .degree v => (R.filter (G.Adj v)).card - 3
  | .star _ _ => 1

def coefficient (R : Finset V) : Row V → V → ℕ
  | .degree v, x => (if v = x then (R.filter (G.Adj v)).card - 3 else 0) +
      (if G.Adj v x then 1 else 0)
  | .star v leaves, x => if x ∈ insert v leaves then 1 else 0

def Valid (R : Finset V) : Row V → Prop
  | .degree v => v ∈ R
  | .star v leaves => leaves.card = 4 ∧ (∀ x ∈ leaves, G.Adj v x) ∧ insert v leaves ⊆ R

instance (R : Finset V) (row : Row V) : Decidable (Valid G R row) := by
  cases row <;> unfold Valid <;> infer_instance

private theorem row_lower (R S : Finset V) (hS : S ⊆ R)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ 3)
    (row : Row V) (hrow : Valid G R row) :
    demand G R row ≤ ∑ x ∈ R \ S, coefficient G R row x := by
  cases row with
  | degree v =>
    by_cases hv : v ∈ S
    · have hf : (R \ S).filter (G.Adj v) = R.filter (G.Adj v) \ S.filter (G.Adj v) := by
        ext x
        simp only [mem_filter, mem_sdiff]
        tauto
      have hd := hdeg v hv
      have hs := card_le_card (filter_subset_filter (G.Adj v) hS)
      have hc := card_sdiff_of_subset (filter_subset_filter (G.Adj v) hS)
      have he : ∑ x ∈ R \ S, coefficient G R (.degree v) x =
          ((R \ S).filter (G.Adj v)).card := by
        rw [card_filter]
        apply sum_congr rfl
        intro x hx
        have hne : v ≠ x := fun h => (mem_sdiff.mp hx).2 (h ▸ hv)
        simp [coefficient, hne]
      rw [he, hf, hc]
      change (R.filter (G.Adj v)).card - 3 ≤ _
      omega
    · have hmem := mem_sdiff.mpr ⟨hrow, hv⟩
      have h := single_le_sum (f := coefficient G R (.degree v))
        (fun _ _ => Nat.zero_le _) hmem
      simpa [demand, coefficient] using h
  | star v leaves =>
    obtain ⟨hfour, hadj, hsub⟩ := hrow
    obtain ⟨x, hx⟩ := GrayPairCutCounting.star_has_omission G S leaves v hfour hadj hdeg
    have ⟨hstar, hnot⟩ := mem_sdiff.mp hx
    have hmem := mem_sdiff.mpr ⟨hsub hstar, hnot⟩
    have h := single_le_sum (f := coefficient G R (.star v leaves))
      (fun _ _ => Nat.zero_le _) hmem
    simpa [demand, coefficient, hstar] using h

/-- If each omitted vertex contributes at most the scaling factor to a
weighted sum of valid rows, that sum bounds the total number of omissions. -/
theorem weighted_omissions {ι : Type*} [Fintype ι]
    (R S : Finset V) (hS : S ⊆ R)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ 3)
    (rows : ι → Row V) (weight : ι → ℕ) (scale : ℕ)
    (hrows : ∀ i, Valid G R (rows i))
    (hload : ∀ x ∈ R, (∑ i, weight i * coefficient G R (rows i) x) ≤ scale) :
    (∑ i, weight i * demand G R (rows i)) ≤ scale * (R.card - S.card) := by
  calc
    _ ≤ ∑ i, weight i * ∑ x ∈ R \ S, coefficient G R (rows i) x :=
      sum_le_sum fun i _ => Nat.mul_le_mul_left _ (row_lower G R S hS hdeg _ (hrows i))
    _ = ∑ x ∈ R \ S, ∑ i, weight i * coefficient G R (rows i) x := by
      simp only [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ _x ∈ R \ S, scale :=
      sum_le_sum fun x hx => hload x (mem_sdiff.mp hx).1
    _ = _ := by simp [card_sdiff_of_subset hS, mul_comm]

end D5.S3.Combinatorics.Graph.HypercubeCritical.GrayOmissionCounting
