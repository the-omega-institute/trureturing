/- GID: D5/S3/SpinModels/KingDefects/KingClosedForm
   generality: G
   mirror-B: D5/B/S3/SpinModels/KingDefects/KingClosedForm
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: none
   digest: Closed counts of one-defect king colourings in arbitrary dimensions. -/
/-
admission_basis: escape-witness
escape_witness: closed_form, width_two, width_three (the diagonal and horizontal
  slot bijections expanded through this delivery give the literal colouring counts).
symmetry: proof_shape=content; consumers=width_three
closed_form: proof_shape=content; consumers=HardinA229574.result,HardinA229575.result,
  HardinA229576.result,HardinA229577.result,HardinA229571.result
width_two: proof_shape=content; consumers=width_three,HardinA229572.result
width_three: proof_shape=content; consumers=HardinA229573.result,HardinA229571.result
All dimensions are unbounded; no bounded enumeration, checker, numerical
reduction or certified instance is asserted.
-/
import D5.S3.SpinModels.KingDefects.KingDiagonal
import D5.S3.SpinModels.KingDefects.KingHorizontal

/-! Counts from the exact horizontal and diagonal slot decompositions. -/
namespace D5.S3.SpinModels.KingDefects.KingClosedForm
open KingGrid KingDifference KingDiagonal KingHorizontal

theorem symmetry (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) : T n k = T k n := by
  have hL : L n k = L k n := by
    rw [count_by_edge, count_by_edge]
    rw [← transposeEdge.sum_comp]
    apply Finset.sum_congr rfl
    intro e _
    exact (Nat.card_congr (transposeDefectEquiv e)).symm
  rw [labelled_eq_twentyFour n k hn hk, labelled_eq_twentyFour k n hk hn] at hL
  omega

theorem closed_form (n k : ℕ) (hn : 4 ≤ n) (hk : 4 ≤ k) :
    4 * (T n k : ℤ) =
      ((n : ℤ)*k-n+6*k+12)*2^n + ((n : ℤ)*k-k+6*n+12)*2^k +
        16*(n : ℤ)*k-64*n-64*k-32 := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 4 := ⟨n-4, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 4 := ⟨k-4, by omega⟩
  have h := count_by_kind (a+3) (b+3) (by omega) (by omega)
  have h₁ := horizontal_sum a (b+1)
  have h₂ := horizontal_sum b (a+1)
  have hd := N_D_closed (a+3) (b+3) (by omega) (by omega)
  have h' := congrArg (fun x : ℕ => (x : ℤ)) h
  have h₁' := congrArg (fun x : ℕ => (x : ℤ)) h₁
  have h₂' := congrArg (fun x : ℕ => (x : ℤ)) h₂
  push_cast at h' h₁' h₂' hd ⊢
  simp only [pow_succ] at h' h₁' h₂' hd ⊢
  nlinarith [h', h₁', h₂', hd]

theorem width_two (n : ℕ) (hn : 2 ≤ n) :
    (T n 2 : ℤ) = (7*(n : ℤ)-8)*2^(n-2) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n-2, by omega⟩
  have h := count_by_kind (p+1) 1 (by omega) (by omega)
  rw [horizontal_two_columns, horizontal_two_rows, N_D_two_columns] at h
  have h' := congrArg (fun x : ℕ => (x : ℤ)) h
  push_cast at h' ⊢
  simp only [Nat.add_sub_cancel, pow_succ] at h' ⊢
  nlinarith [h']

theorem width_three (n : ℕ) (hn : 2 ≤ n) :
    4*(T n 3 : ℤ) = (3*(n : ℤ)+27)*2^n+44*n-116 := by
  by_cases h2 : n = 2
  · subst n
    rw [symmetry 2 3 (by omega) (by omega), width_two 3 (by omega)]
    norm_num
  by_cases h3 : n = 3
  · subst n
    have h := count_by_kind 2 2 (by omega) (by omega)
    have hh := horizontal_three_rows 1
    have hd := N_D_closed 2 2 (by omega) (by omega)
    norm_num at hh hd h ⊢
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    have hh' := congrArg (fun x : ℕ => (x : ℤ)) hh
    push_cast at h' hh'
    omega
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n-4, by omega⟩
    have h := count_by_kind (p+3) 2 (by omega) (by omega)
    have h₁ := horizontal_sum p 0
    have h₂ := horizontal_three_rows (p+2)
    have hd := N_D_closed (p+3) 2 (by omega) (by omega)
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    have h₁' := congrArg (fun x : ℕ => (x : ℤ)) h₁
    have h₂' := congrArg (fun x : ℕ => (x : ℤ)) h₂
    push_cast at h' h₁' h₂' hd ⊢
    norm_num [pow_succ] at h' h₁' h₂' hd ⊢
    nlinarith [h', h₁', h₂', hd]

#print axioms symmetry
#print axioms closed_form
#print axioms width_two
#print axioms width_three
end D5.S3.SpinModels.KingDefects.KingClosedForm
