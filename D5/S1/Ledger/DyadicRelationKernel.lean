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

/-! A finitely supported vector is reconstructed from its lower dyadic rows and
the remaining endpoint coefficient. -/
theorem support_bounded_decomposition (u : V) (m : ℕ)
    (h : u.support ⊆ Finset.range (m + 1)) :
    u = (Finset.sum (Finset.range m) (fun j => u j • t j m)) + weighted u m • eps m := by
  classical
  ext n
  by_cases hn : n < m
  · have hnm : n ∈ Finset.range m := Finset.mem_range.mpr hn
    have hsum : Finset.sum (Finset.range m) (fun j => (u j • t j m) n) = (u n • t n m) n := by
      apply Finset.sum_eq_single_of_mem n hnm
      intro b hb hbn
      simp [t, eps, Finsupp.single_apply, hbn, Nat.ne_of_lt hn]
    have hsum_eval : (Finset.sum (Finset.range m) (fun j => u j • t j m)) n = (u n • t n m) n := by
      calc
        (Finset.sum (Finset.range m) (fun j => u j • t j m)) n =
            (Finset.sum (Finset.range m) (fun j => fun x => (u j • t j m) x)) n :=
          congrFun (Finsupp.coe_finset_sum (Finset.range m) (fun j => u j • t j m)) n
        _ = Finset.sum (Finset.range m) (fun j => (u j • t j m) n) := by
          exact Finset.sum_apply n (Finset.range m) (fun j => fun x => (u j • t j m) x)
        _ = (u n • t n m) n := hsum
    simp only [Finsupp.add_apply, Finsupp.smul_apply]
    rw [hsum_eval]
    simp [t, eps, Finsupp.single_apply, hn, Nat.ne_of_lt hn]
  · by_cases hnm : n = m
    · subst n
      simp [Finset.sum_apply, t, eps, Finsupp.single_apply, weighted,
        Finset.sum_range_succ, Finset.mem_range]
      have hif : (Finset.sum (Finset.range m) (fun x => u x * if x = m then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxm : x ≠ m := Nat.ne_of_lt (Finset.mem_range.mp hx)
        simp [hxm]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [hif]
      have hrev : (Finset.sum (Finset.range m) (fun x => u x * 2 ^ (m - x))) =
          Finset.sum (Finset.range m) (fun x => 2 ^ (m - x) * u x) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hrev]
      ring
    · have hgt : m < n := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm hnm)
      have hzero : u n = 0 := by
        by_contra hz
        have hs : n ∈ u.support := by simpa [Finsupp.mem_support_iff, hz]
        have hlt := Finset.mem_range.mp (h hs)
        omega
      simp [Finset.sum_apply, t, eps, Finsupp.single_apply, hzero, Nat.ne_of_gt hgt]

end
end D5.S1.Ledger.DyadicRelationKernel
