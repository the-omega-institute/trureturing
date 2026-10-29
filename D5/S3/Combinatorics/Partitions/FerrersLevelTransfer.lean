/- GID: D5/S3/Combinatorics/Partitions/FerrersLevelTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/FerrersLevelTransfer
   mirror-E: none(waiver:gaussian-level-transfer)
   anchors: [D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle]
   utility: none
   digest: Gaussian coefficients count bounded level transitions with a fixed last row. -/

import D5.S3.Combinatorics.CylindricPartition.LiUncuRectangle
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
open Polynomial
open D5.S3.Combinatorics.CylindricPartition.LiUncuDefs
open D5.S3.Combinatorics.CylindricPartition.LiUncu
open scoped BigOperators

/-- A single level has r+1 rows; its last row has length v. -/
abbrev Level (r U u v a : ℕ) :=
  {x : Fin (r+1) → Fin (U+1) // Antitone x ∧
    (∀ i, (x i).val ≤ u) ∧ (x (Fin.last r)).val = v ∧
    ∑ i, (x i).val = a}

private abbrev Rectangle (r d : ℕ) := {x : Fin r → Fin (d+1) // Antitone x}

private theorem gaussian_coefficient (r d k : ℕ) :
    (gauss (d+r) r).coeff k =
      (Fintype.card {x : Rectangle r d // ∑ j, (x.val j).val = k} : ℤ) := by
  classical
  rw [gauss_rectangle, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Fintype.card_subtype]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  simp [eq_comm]

private def levelRectangleEquiv (r U u v a : ℕ) (hu : u ≤ U) (hv : v ≤ u)
    (ha : (r+1)*v ≤ a) :
    Level r U u v a ≃
      {x : Rectangle r (u-v) // ∑ j, (x.val j).val = a-(r+1)*v} where
  toFun x := ⟨⟨fun j => ⟨(x.val j.castSucc).val-v, by
      have := x.property.2.1 j.castSucc
      omega⟩, by
      intro i j hij
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.sub_le_sub_right
        (Fin.le_iff_val_le_val.mp (x.property.1 (by simpa using hij))) v⟩, by
    have hlo (j : Fin (r+1)) : v ≤ (x.val j).val := by
      have hb := Fin.le_iff_val_le_val.mp (x.property.1 (Fin.le_last j))
      have he := x.property.2.2.1
      omega
    have hs : (∑ j : Fin r, ((x.val j.castSucc).val-v)) + (r+1)*v = a := by
      have ht := x.property.2.2.2
      rw [Fin.sum_univ_castSucc] at ht
      have hend := x.property.2.2.1
      have he : (∑ j : Fin r, ((x.val j.castSucc).val-v)) + r*v =
          ∑ j : Fin r, (x.val j.castSucc).val := by
        calc
          _ = ∑ j : Fin r, ((x.val j.castSucc).val-v+v) := by
            rw [Finset.sum_add_distrib]; simp
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            exact Nat.sub_add_cancel (hlo j.castSucc)
      rw [Nat.add_mul, one_mul]
      omega
    change (∑ j : Fin r, ((x.val j.castSucc).val-v)) = a-(r+1)*v
    omega⟩
  invFun x := ⟨Fin.lastCases (⟨v, Nat.lt_succ_of_le (hv.trans hu)⟩ : Fin (U+1))
      (fun j : Fin r => (⟨(x.val.val j).val+v, Nat.lt_succ_of_le
        ((Nat.add_le_add_right (Nat.le_of_lt_succ (x.val.val j).isLt) v).trans
          ((Nat.le_of_eq (Nat.sub_add_cancel hv)).trans hu))⟩ : Fin (U+1))), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      cases i using Fin.lastCases with
      | last =>
          have hj : j = Fin.last r := le_antisymm (Fin.le_last _) hij
          subst j
          exact le_rfl
      | cast i =>
          cases j using Fin.lastCases with
          | last => simp [Fin.le_iff_val_le_val]
          | cast j =>
              apply Fin.le_iff_val_le_val.mpr
              simpa using Nat.add_le_add_right
                (Fin.le_iff_val_le_val.mp (x.val.property (by simpa using hij))) v
    · intro i
      cases i using Fin.lastCases with
      | last => simpa using hv
      | cast j => simp; have := (x.val.val j).isLt; omega
    · simp
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [x.property]
      have hm : (r+1)*v = r*v+v := by ring
      omega⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    cases j using Fin.lastCases with
    | last => apply Fin.ext; simpa using x.property.2.2.1.symm
    | cast j =>
        apply Fin.ext
        dsimp only
        simp only [Fin.lastCases_castSucc]
        change (x.val j.castSucc).val-v+v = (x.val j.castSucc).val
        apply Nat.sub_add_cancel
        have hb := Fin.le_iff_val_le_val.mp (x.property.1 (Fin.le_last j.castSucc))
        have he := x.property.2.2.1
        omega
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    apply Fin.ext
    dsimp only
    simp only [Fin.lastCases_castSucc]
    change (x.val.val j).val+v-v = (x.val.val j).val
    omega

/-- A finite arithmetic transition entry; the Gaussian polynomial is given by q-Pascal. -/
def transition (r U a : ℕ) (u v : Fin (U+1)) : ℤ :=
  if v.val ≤ u.val ∧ (r+1)*v.val ≤ a then
    (gauss (u.val-v.val+r) r).coeff (a-(r+1)*v.val) else 0

/-- Every fixed-endpoint level fiber is counted by the guarded Gaussian coefficient. -/
theorem level_card (r U a : ℕ) (u v : Fin (U+1)) :
    (Fintype.card (Level r U u.val v.val a) : ℤ) = transition r U a u v := by
  classical
  unfold transition
  split_ifs with h
  · rw [gaussian_coefficient]
    exact_mod_cast Fintype.card_congr
      (levelRectangleEquiv r U u.val v.val a (Nat.le_of_lt_succ u.isLt) h.1 h.2)
  · have hn : IsEmpty (Level r U u.val v.val a) := ⟨by
      intro x
      apply h
      refine ⟨?_, ?_⟩
      · have hlast := x.property.2.2.1
        have hbound := x.property.2.1 (Fin.last r)
        omega
      · have ht := x.property.2.2.2
        have hs : (r+1)*v.val ≤ ∑ j, (x.val j).val := by
          calc
            (r+1)*v.val = ∑ _j : Fin (r+1), v.val := by simp
            _ ≤ _ := Finset.sum_le_sum (fun j _ => by
              have hb := Fin.le_iff_val_le_val.mp (x.property.1 (Fin.le_last j))
              have he := x.property.2.2.1
              omega)
        omega⟩
    letI := hn
    simp

end D5.S3.Combinatorics.Partitions.FerrersLevelTransfer
