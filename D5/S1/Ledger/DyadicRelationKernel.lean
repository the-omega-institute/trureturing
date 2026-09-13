/- GID: D5/S1/Ledger/DyadicRelationKernel
   generality: G
   mirror-B: D5/B/S1/Ledger/DyadicRelationKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The dyadic adjacent-row relation admits a telescoping kernel decomposition and exact readout kernel. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
namespace D5.S1.Ledger.DyadicRelationKernel
noncomputable section

abbrev V := ℕ →₀ ℤ
def eps (n : ℕ) : V := Finsupp.single n 1
def row (n : ℕ) : V := eps n - (2 : ℤ) • eps (n + 1)
def H : Submodule ℤ V := Submodule.span ℤ (Set.range row)
def ell (u : V) : ℚ := u.sum (fun n z => (z : ℚ) / (2 : ℚ) ^ n)
def t (j m : ℕ) : V := eps j - (2 : ℤ) ^ (m - j) • eps m
def weighted (u : V) (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) (fun j => (2 : ℤ) ^ (m - j) * u j)

/-! The telescoping row from index `j` to index `m` belongs to the adjacent-row span. -/
theorem telescoping_mem (j d : ℕ) : t j (j + d) ∈ H := by
  let p : ℕ → Prop := fun d => t j (j + d) ∈ H
  have hp : p 0 := by simp [p, t, H]
  have hs : ∀ d, p d → p (d + 1) := by
    intro d ih
    change t j (j + d) ∈ H at ih
    change t j (j + (d + 1)) ∈ H
    rw [show t j (j + (d + 1)) = t j (j + d) + (2 : ℤ) ^ d • row (j + d) by
      simp [t, row, eps, sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm,
        pow_succ]]
    exact H.add_mem ih (H.smul_mem _ (Submodule.subset_span ⟨j + d, rfl⟩))
  exact Nat.rec hp (fun d ih => hs d ih) d

end
end D5.S1.Ledger.DyadicRelationKernel
