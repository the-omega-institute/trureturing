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

/-- The group of finitely supported integer coordinate vectors. -/
abbrev V := ℕ →₀ ℤ
/-- The coordinate vector with coefficient one at index `n`. -/
def eps (n : ℕ) : V := Finsupp.single n 1
/-- The adjacent relation between a coordinate and twice its successor. -/
def row (n : ℕ) : V := eps n - (2 : ℤ) • eps (n + 1)
/-- The integer span of the adjacent relations. -/
def H : Submodule ℤ V := Submodule.span ℤ (Set.range row)
/-- Evaluation with reciprocal powers of two as coordinate weights. -/
def ell (u : V) : ℚ := u.sum (fun n z => (z : ℚ) / (2 : ℚ) ^ n)
/-- The endpoint difference between indices `j` and `m`. -/
def t (j m : ℕ) : V := eps j - (2 : ℤ) ^ (m - j) • eps m
/-- The integer numerator obtained by using the common denominator `2^m`. -/
def weighted (u : V) (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) (fun j => (2 : ℤ) ^ (m - j) * u j)

/-- The telescoping row from index `j` to index `m` belongs to the adjacent-row span. -/
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

/-- A finitely supported vector is reconstructed from its lower dyadic rows and
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

/-- A vector lies in the span of the adjacent relations exactly when its dyadic evaluation is zero. -/
theorem mem_H_iff_eval_eq_zero (u : V) : u ∈ H ↔ ell u = 0 := by
  classical
  let f : V →+ ℚ :=
    { toFun := ell
      map_zero' := by simp [ell]
      map_add' := fun v w => Finsupp.sum_add_index' (by simp)
        (by intros; simp [Int.cast_add, add_div]) }
  have heps (n : ℕ) : f (eps n) = 1 / (2 : ℚ) ^ n := by
    change ell (eps n) = _
    simp [ell, eps]
  have hH (v : V) (hv : v ∈ H) : f v = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨n, rfl⟩ := hv
      simp only [row, map_sub, map_zsmul, heps, zsmul_eq_mul, Int.cast_ofNat]
      rw [pow_succ]
      field_simp
      <;> ring
    | zero => exact f.map_zero
    | add v w hv hw ihv ihw => simp [map_add, ihv, ihw]
    | smul a v hv ih => simp only [map_zsmul, ih, smul_zero]
  constructor
  · exact hH u
  · intro hu
    let m := u.support.sup id
    have hm : u.support ⊆ Finset.range (m + 1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    have hs : (∑ j ∈ Finset.range m, u j • t j m) ∈ H := by
      apply H.sum_mem
      intro j hj
      apply H.smul_mem
      have hjm := Nat.le_of_lt (Finset.mem_range.mp hj)
      simpa only [Nat.add_sub_of_le hjm] using telescoping_mem j (m - j)
    have hd := support_bounded_decomposition u m hm
    have hz : f u = 0 := hu
    have he := congrArg f hd
    rw [map_add, hH _ hs, map_zsmul, heps, hz, zero_add, zsmul_eq_mul] at he
    have hw : weighted u m = 0 := by
      have hc : (weighted u m : ℚ) = 0 :=
        (mul_eq_zero.mp he.symm).resolve_right (by positivity)
      exact_mod_cast hc
    rw [hd, hw, zero_smul, add_zero]
    exact hs

end
end D5.S1.Ledger.DyadicRelationKernel
