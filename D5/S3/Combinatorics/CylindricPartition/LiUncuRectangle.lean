/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuRectangle
   mirror-E: none(waiver:weighted-rectangle-bijection)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: A reversible largest-part decomposition enumerates Gaussian rectangles. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuGaussian
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncu

open Polynomial LiUncuDefs

/-- Weakly decreasing tuples in a rectangle have the Gaussian weight enumerator. -/
theorem gauss_rectangle (M m : ℕ) :
    gauss (M + m) m =
      ∑ v : {v : Fin m → Fin (M + 1) // Antitone v}, X ^ (∑ j, (v.val j).val) := by
  classical
  have empty (M : ℕ) :
      (∑ v : {v : Fin 0 → Fin (M + 1) // Antitone v},
        (X : ℤ[X]) ^ (∑ j, (v.val j).val)) = 1 := by
    let v : {v : Fin 0 → Fin (M + 1) // Antitone v} :=
      ⟨fun j => Fin.elim0 j, fun a => Fin.elim0 a⟩
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      have : w = v := Subtype.ext (funext fun j => Fin.elim0 j)
      exact (hw this).elim
    · simp
  induction M generalizing m with
  | zero =>
      let v : {v : Fin m → Fin 1 // Antitone v} := ⟨fun _ => 0, fun _ _ _ => le_rfl⟩
      have diagonal (a : ℕ) : gauss a a = 1 := by
        induction a with
        | zero => rfl
        | succ a ih =>
            rw [gauss, gauss_zero_of_lt a (a + 1) (by omega), Nat.sub_self]
            simpa using ih
      rw [zero_add, diagonal]
      symm
      rw [Finset.sum_eq_single v]
      · simp [v]
      · intro w _ hw
        have : w = v := Subtype.ext (funext fun _ => Subsingleton.elim _ _)
        exact (hw this).elim
      · simp
  | succ M ihM =>
      induction m with
      | zero => simpa [gauss] using (empty (M + 1)).symm
      | succ m ihm =>
          let Big := {v : Fin (m + 1) → Fin (M + 2) // Antitone v}
          let Small := {v : Fin (m + 1) → Fin (M + 1) // Antitone v}
          let Tail := {v : Fin m → Fin (M + 2) // Antitone v}
          let shrink (v : Big) (h : (v.val 0).val < M + 1) : Small :=
            ⟨fun j => ⟨(v.val j).val, by
                have hj := v.property (Fin.zero_le j)
                have hj' := Fin.le_iff_val_le_val.mp hj
                omega⟩,
              fun a b hab => Fin.le_iff_val_le_val.mpr
                (Fin.le_iff_val_le_val.mp (v.property hab))⟩
          let widen (v : Small) : Big :=
            ⟨fun j => (v.val j).castSucc,
              fun a b hab => Fin.le_iff_val_le_val.mpr
                (Fin.le_iff_val_le_val.mp (v.property hab))⟩
          let drop (v : Big) : Tail :=
            ⟨Fin.tail v.val, fun a b hab => v.property (by simpa using hab)⟩
          let adjoin (v : Tail) : Big :=
            ⟨Fin.cons ⟨M + 1, by omega⟩ v.val, by
              intro a b hab
              cases a using Fin.cases with
              | zero =>
                  apply Fin.le_iff_val_le_val.mpr
                  simp only [Fin.cons_zero]
                  exact Nat.le_of_lt_succ (Fin.isLt _)
              | succ a =>
                  cases b using Fin.cases with
                  | zero => simp at hab
                  | succ b =>
                      simp only [Fin.cons_succ]
                      exact v.property (by simpa using hab)⟩
          let e : Big ≃ Small ⊕ Tail :=
            { toFun := fun v =>
                if h : (v.val 0).val < M + 1 then Sum.inl (shrink v h) else Sum.inr (drop v)
              invFun := Sum.elim widen adjoin
              left_inv := by
                intro v
                dsimp
                split_ifs with h
                · apply Subtype.ext
                  funext j
                  apply Fin.ext
                  rfl
                · apply Subtype.ext
                  funext j
                  cases j using Fin.cases with
                  | zero =>
                      apply Fin.ext
                      change M + 1 = (v.val 0).val
                      have hv := (v.val 0).isLt
                      omega
                  | succ j => simp [adjoin, drop, Fin.tail]
              right_inv := by
                intro s
                cases s with
                | inl v =>
                    have h : ((widen v).val 0).val < M + 1 := (v.val 0).isLt
                    dsimp
                    rw [dif_pos h]
                    rfl
                | inr v =>
                    have h : ¬((adjoin v).val 0).val < M + 1 := by
                      simp [adjoin]
                    dsimp
                    rw [dif_neg h]
                    rfl }
          have weights :
              (∑ v : Big, (X : ℤ[X]) ^ (∑ j, (v.val j).val)) =
                (∑ v : Small, X ^ (∑ j, (v.val j).val)) +
                  X ^ (M + 1) * ∑ v : Tail, X ^ (∑ j, (v.val j).val) := by
            rw [← e.symm.sum_comp (fun v => (X : ℤ[X]) ^ (∑ j, (v.val j).val))]
            rw [Fintype.sum_sum_type]
            change (∑ v : Small, X ^ (∑ j, ((widen v).val j).val)) +
                (∑ v : Tail, X ^ (∑ j, ((adjoin v).val j).val)) = _
            have hsmall :
                (∑ v : Small, (X : ℤ[X]) ^ (∑ j, ((widen v).val j).val)) =
                  ∑ v : Small, X ^ (∑ j, (v.val j).val) := rfl
            rw [hsmall, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro v _
            simp only [adjoin, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
            exact pow_add _ _ _
          have hindex : M + 1 + (m + 1) = (M + (m + 1)) + 1 := by omega
          rw [hindex, gauss]
          rw [show M + (m + 1) - m = M + 1 by omega, ihM (m + 1)]
          have htail := ihm
          rw [show M + 1 + m = M + (m + 1) by omega] at htail
          rw [htail]
          exact weights.symm

end D5.S3.Combinatorics.CylindricPartition.LiUncu
